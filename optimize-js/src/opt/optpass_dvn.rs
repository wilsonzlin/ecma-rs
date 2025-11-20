use crate::cfg::cfg::Cfg;
use crate::dom::Dom;
use crate::eval::consteval::maybe_eval_const_bin_expr;
use crate::eval::consteval::maybe_eval_const_builtin_call;
use crate::eval::consteval::maybe_eval_const_builtin_val;
use crate::il::inst::Arg;
use crate::il::inst::BinOp;
use crate::il::inst::Const;
use crate::il::inst::Inst;
use crate::il::inst::InstTyp;
use crate::il::inst::UnOp;
use ahash::HashMap;
use ahash::HashSet;
use itertools::Itertools;
use std::collections::hash_map::Entry;
use std::mem::swap;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Val {
  Bin { left: Arg, op: BinOp, right: Arg },
  Un { op: UnOp, arg: Arg },
}

#[derive(Clone, Default)]
struct State {
  val_to_coc: HashMap<Val, Arg>,
  tgt_to_coc: HashMap<u32, Arg>,
}

impl State {
  /// If this is the first instance/computation of $val, all future uses will use $available_at_tgt instead.
  pub fn upsert_val(&mut self, val: Val, available_at_tgt: u32) -> (Arg, Option<Arg>) {
    match self.val_to_coc.entry(val) {
      Entry::Occupied(o) => (o.get().clone(), Some(o.get().clone())),
      Entry::Vacant(v) => {
        v.insert(Arg::Var(available_at_tgt));
        (Arg::Var(available_at_tgt), None)
      }
    }
  }

  pub fn canon_arg(&mut self, arg: &Arg) -> Arg {
    match arg {
      Arg::Builtin(p) => match maybe_eval_const_builtin_val(p) {
        Some(value) => Arg::Const(value),
        None => Arg::Builtin(p.clone()),
      },
      Arg::Const(c) => Arg::Const(c.clone()),
      Arg::Fn(id) => Arg::Fn(*id),
      Arg::Var(tgt) => match self.tgt_to_coc.entry(*tgt) {
        Entry::Occupied(o) => o.get().clone(),
        // We haven't seen this variable before, so it must be from a back edge. Therefore, we must leave it as is.
        Entry::Vacant(_) => Arg::Var(*tgt),
      },
    }
  }
}

fn inner(changed: &mut bool, state: &mut State, cfg: &mut Cfg, dom: &Dom, label: u32) {
  let orig_state = state.clone();
  for inst_mut in cfg.bblocks.get_mut(label).iter_mut() {
    // We still need to normalise args in instructions in case we don't rewrite entire instruction to a VarAssign.
    // Do a `&*` to ensure we don't mutate `inst` within the `match`. (Important as changes must be marked, so we should have one place for changing.)
    let inst = &mut *inst_mut;
    let mut new_inst = inst.clone();

    // In the original Keith-Cooper paper, phis are processed first. This is still the case here, as Phi instructions are always first.

    // Stage 1: canonicalize args.
    for arg in new_inst.args.iter_mut() {
      *arg = state.canon_arg(arg);
    }

    // Stage 2: consteval opportunities.
    // Consteval doesn't always result in Const. It can result in Arg::Builtin if we're accessing a builtin's property, for example. Therefore this results in Arg and not Const.
    let consteval = match new_inst.t {
      InstTyp::Bin => {
        let (_, mut left, op, mut right) = new_inst.as_bin();
        // Remember: `a + b` isn't commutative if either is a string.
        let commutative = match (op, left, right) {
          (BinOp::Add, Arg::Const(Const::Num(_)), Arg::Const(Const::Num(_))) => true,
          (BinOp::Mul, Arg::Const(Const::Num(_)), Arg::Const(Const::Num(_))) => true,
          _ => false,
        };
        if commutative && left > right {
          swap(&mut left, &mut right);
        };
        match (op, left, right) {
          (op, Arg::Const(l), Arg::Const(r)) => maybe_eval_const_bin_expr(op, l, r).map(Arg::Const),
          (BinOp::GetProp, Arg::Builtin(o), Arg::Const(Const::Str(p))) => {
            Some(Arg::Builtin(format!("{o}.{p}")))
          }
          _ => None,
        }
      }
      InstTyp::Call => {
        let (tgt, func, this, args, spreads) = inst.as_call();
        // TODO If constevalable and `tgt` is None.
        match (tgt, func, this, args, spreads) {
          (Some(_), Arg::Builtin(func), _, args, spread)
            if spreads.is_empty() && args.iter().all(|a| matches!(a, Arg::Const(_))) =>
          {
            maybe_eval_const_builtin_call(&func, &args.iter().map(|a| a.to_const()).collect_vec())
              .map(|v| Arg::Const(v))
          }
          _ => None,
        }
      }
      _ => None,
    };

    // Stage 3: DVN.
    // If we have a consteval value, get its canonical representation and replace our Inst with a VarAssign to it.
    // If we don't, and our Inst is pure and has already been computed before, also replace it.
    if let Some(value) = consteval {
      let tgt = new_inst.tgts[0];
      assert!(state.tgt_to_coc.insert(tgt, value.clone()).is_none());
      new_inst = Inst::var_assign(tgt, value)
    } else {
      let pure_val = match new_inst.t {
        InstTyp::Bin => {
          let (_, left, op, right) = new_inst.as_bin();
          Some(Val::Bin {
            left: left.clone(),
            op,
            right: right.clone(),
          })
        }
        InstTyp::Un => {
          let (tgt, op, arg) = new_inst.as_un();
          Some(Val::Un {
            op,
            arg: arg.clone(),
          })
        }
        InstTyp::VarAssign => {
          // We just need to number this var.
          let (tgt, value) = new_inst.as_var_assign();
          assert!(state.tgt_to_coc.insert(tgt, value.clone()).is_none());
          None
        }
        // Only pure functions can be reused, and we pessimistically assume all functions are non-pure.
        InstTyp::Call => None,
        _ => None,
      };
      if let Some(val) = pure_val {
        let tgt = new_inst.tgts[0];
        let (row, existing) = state.upsert_val(val, tgt);
        assert!(state.tgt_to_coc.insert(tgt, row).is_none());
        if let Some(value) = existing {
          new_inst = Inst::var_assign(tgt, value);
        };
      };
    };

    if inst != &new_inst {
      *changed = true;
      *inst = new_inst;
    };
  }

  for s in cfg.graph.children(label) {
    for inst in cfg.bblocks.get_mut(s).iter_mut() {
      if inst.t != InstTyp::Phi {
        // No more phi nodes.
        break;
      };
      // TODO Is the following algorithm correct?
      let Some(ex) = inst.remove_phi(label) else {
        continue;
      };
      let coc = state.canon_arg(&ex);
      if ex != coc {
        *changed = true;
      };
      inst.insert_phi(label, coc);
    }
  }

  for c in dom.immediately_dominated_by(label) {
    inner(changed, state, cfg, dom, c);
  }

  *state = orig_state;
}

/// Dominator-based value numbering.
/// - https://www.cs.tufts.edu/~nr/cs257/archive/keith-cooper/value-numbering.pdf
/// - https://www.cs.cornell.edu/courses/cs6120/2019fa/blog/global-value-numbering/
///
/// This performs:
///
/// - Common subexpression elimination
/// - Copy propagation
/// - Const propagation
/// - Const evaluation
pub fn optpass_dvn(changed: &mut bool, cfg: &mut Cfg, dom: &Dom) {
  let mut state = State::default();
  inner(changed, &mut state, cfg, dom, 0);
}
