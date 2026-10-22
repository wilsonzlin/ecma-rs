//! Regression tests for the built-in globals added by the vm-js built-ins program:
//! `Math` (§21.3), `parseInt`/`parseFloat`/`isFinite` (§19.2), `Number` statics
//! (§21.1.2), `String.fromCharCode` (§22.1.2.1), `Object.prototype.hasOwnProperty`
//! + `Object.getOwnPropertyDescriptor`/`getOwnPropertyNames` (§20.1), and BigInt
//! bitwise/shift operators (§6.1.6.2.18–.22).
//!
//! Expected values are derived from ECMA-262, not from the interpreter's output.

use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

fn eval(src: &str) -> Value {
  new_runtime().exec_script(src).unwrap()
}

fn assert_true(src: &str) {
  assert_eq!(eval(src), Value::Bool(true), "expected `{src}` to be true");
}

// --- BigInt bitwise & shift (ECMA-262 §6.1.6.2.18–.22) ---

#[test]
fn bigint_bitwise_and_or_xor_nonnegative() {
  // Truth tables from §6.1.6.2.20–.22 over small operands.
  assert_true("(0b01n & 0b11n) === 0b01n");
  assert_true("(0b10n & 0b01n) === 0b00n");
  assert_true("(0b10n | 0b01n) === 0b11n");
  assert_true("(0b11n ^ 0b01n) === 0b10n");
  assert_true("(0xffffffffffffffffn & 0xffffffffffffffffn) === 0xffffffffffffffffn");
}

#[test]
fn bigint_bitwise_with_negatives_uses_twos_complement() {
  // §6.1.6.2: negative BigInts behave as infinite two's-complement integers.
  // -1n is ...1111, so `-1n & x === x`.
  assert_true("(-1n & 5n) === 5n");
  // -2n is ...11110; AND 3n (0b011) → 0b010 = 2n.
  assert_true("(-2n & 3n) === 2n");
  // -5n is ...11011; AND 3n (0b011) → 0b011 = 3n.
  assert_true("(-5n & 3n) === 3n");
  // -1n | 0n === -1n; sign extension propagates.
  assert_true("(-1n | 0n) === -1n");
  // XOR extends the sign: -1n ^ -1n === 0n.
  assert_true("(-1n ^ -1n) === 0n");
}

#[test]
fn bigint_shifts() {
  // §6.1.6.2.18/.19: left shift multiplies by 2^n, signed right shift is a floor divide.
  assert_true("(1n << 4n) === 16n");
  assert_true("(3n << 2n) === 12n");
  assert_true("(-3n << 1n) === -6n");
  assert_true("(256n >> 2n) === 64n");
  assert_true("(-8n >> 1n) === -4n");
  // Arithmetic right shift rounds toward -Infinity: floor(-5/2) === -3.
  assert_true("(-5n >> 1n) === -3n");
  // Right shift beyond magnitude collapses to the sign: 0n for non-negatives, -1n for negatives.
  assert_true("(5n >> 10n) === 0n");
  assert_true("(-1n >> 5n) === -1n");
  // A negative shift count reverses the direction.
  assert_true("(1n << -0n) === 1n");
  assert_true("(4n >> -1n) === 8n");
}

#[test]
fn bigint_unsigned_right_shift_throws_type_error() {
  // §6.1.6.2.19 note: BigInts are not fixed-width, so `>>>` throws a TypeError.
  assert_true(
    "let threw=false; try { 1n >>> 1n; } catch (e) { threw = e instanceof TypeError; } threw",
  );
}

// --- Number statics (§21.1.2) ---

#[test]
fn number_predicates_do_not_coerce() {
  // §21.1.2.2/.4: `Number.isNaN`/`isFinite` return false for non-Number arguments (no coercion).
  assert_true("Number.isNaN(NaN) === true");
  assert_true("Number.isNaN(1) === false");
  assert_true("Number.isNaN('NaN') === false");
  assert_true("Number.isFinite(1) === true");
  assert_true("Number.isFinite(Infinity) === false");
  assert_true("Number.isFinite('1') === false");
  // §21.1.2.3/.5
  assert_true("Number.isInteger(5) === true");
  assert_true("Number.isInteger(5.5) === false");
  assert_true("Number.isInteger('5') === false");
  assert_true("Number.isSafeInteger(9007199254740991) === true");
  assert_true("Number.isSafeInteger(9007199254740992) === false");
}

#[test]
fn number_static_constants() {
  // §21.1.2.6/.8/.1
  assert_true("Number.MAX_SAFE_INTEGER === 9007199254740991");
  assert_true("Number.MIN_SAFE_INTEGER === -9007199254740991");
  assert_true("Number.EPSILON === 2 ** -52");
}

// --- Global numeric functions (§19.2) ---

#[test]
fn parse_int_semantics() {
  // §19.2.5
  assert_true("parseInt('42') === 42");
  assert_true("parseInt('10.9') === 10");
  assert_true("parseInt('   -10  ') === -10");
  // Radix 16 default from the `0x` prefix.
  assert_true("parseInt('0x1F') === 31");
  // Explicit radix.
  assert_true("parseInt('11', 2) === 3");
  assert_true("parseInt('z', 36) === 35");
  // No valid digits → NaN.
  assert_true("Number.isNaN(parseInt('xyz'))");
  // Number.parseInt is the same function object (§21.1.2.13).
  assert_true("Number.parseInt === parseInt");
}

#[test]
fn parse_float_semantics() {
  // §19.2.4
  assert_true("parseFloat('3.14') === 3.14");
  assert_true("parseFloat('  .5e1 ') === 5");
  assert_true("parseFloat('10e2xyz') === 1000");
  assert_true("parseFloat('Infinity') === Infinity");
  assert_true("parseFloat('-Infinity') === -Infinity");
  assert_true("Number.isNaN(parseFloat('abc'))");
  assert_true("Number.parseFloat === parseFloat");
}

#[test]
fn is_finite_coerces() {
  // §19.2.2: the global `isFinite` coerces its argument with ToNumber.
  assert_true("isFinite(1) === true");
  assert_true("isFinite('1') === true");
  assert_true("isFinite(NaN) === false");
  assert_true("isFinite(Infinity) === false");
}

// --- Math (§21.3) ---

#[test]
fn math_elementary_functions() {
  assert_true("Math.abs(-5) === 5");
  assert_true("Math.floor(4.7) === 4");
  assert_true("Math.ceil(4.1) === 5");
  assert_true("Math.trunc(-4.7) === -4");
  assert_true("Math.sign(-3) === -1");
  assert_true("Math.sign(0) === 0");
  assert_true("Math.sqrt(16) === 4");
  assert_true("Math.cbrt(27) === 3");
  assert_true("Math.pow(2, 10) === 1024");
  assert_true("Math.hypot(3, 4) === 5");
}

#[test]
fn math_round_rounds_half_toward_positive_infinity() {
  // §21.3.2.28: ties round toward +Infinity, not away from zero.
  assert_true("Math.round(2.5) === 3");
  assert_true("Math.round(-2.5) === -2");
  assert_true("Math.round(2.4) === 2");
}

#[test]
fn math_min_max_and_nan_propagation() {
  // §21.3.2.24/.25
  assert_true("Math.max(1, 2, 3) === 3");
  assert_true("Math.min(1, 2, 3) === 1");
  assert_true("Math.max() === -Infinity");
  assert_true("Math.min() === Infinity");
  assert_true("Number.isNaN(Math.max(1, NaN))");
  assert_true("Number.isNaN(Math.min(NaN, 2))");
}

#[test]
fn math_constants() {
  // §21.3.1
  assert_true("Math.PI > 3.1415 && Math.PI < 3.1416");
  assert_true("Math.E > 2.718 && Math.E < 2.719");
}

// --- String.fromCharCode (§22.1.2.1) ---

#[test]
fn string_from_char_code() {
  assert_true("String.fromCharCode(65) === 'A'");
  assert_true("String.fromCharCode(72, 105) === 'Hi'");
  // ToUint16 wraps modulo 2^16: 65 + 65536 === 'A'.
  assert_true("String.fromCharCode(65601) === 'A'");
  assert_true("String.fromCharCode() === ''");
}

// --- Object introspection (§20.1) ---

#[test]
fn object_has_own_property() {
  // §20.1.3.2
  assert_true("({a: 1}).hasOwnProperty('a') === true");
  assert_true("({a: 1}).hasOwnProperty('b') === false");
  // Inherited properties are not own.
  assert_true("({}).hasOwnProperty('toString') === false");
  // Works on constructor objects (Number is an object with an own MAX_VALUE).
  assert_true("Number.hasOwnProperty('MAX_VALUE') === true");
}

#[test]
fn object_get_own_property_descriptor() {
  // §20.1.2.8
  assert_true("Object.getOwnPropertyDescriptor({a: 5}, 'a').value === 5");
  assert_true("Object.getOwnPropertyDescriptor({a: 5}, 'a').writable === true");
  assert_true("Object.getOwnPropertyDescriptor({a: 5}, 'a').enumerable === true");
  assert_true("Object.getOwnPropertyDescriptor({a: 5}, 'missing') === undefined");
}

#[test]
fn object_get_own_property_names() {
  // §20.1.2.10: own String keys, enumerable or not.
  assert_true("Object.getOwnPropertyNames({a: 1, b: 2}).length === 2");
  assert_true("Object.getOwnPropertyNames({a: 1, b: 2})[0] === 'a'");
}

// --- Wrapper valueOf receiver coercion throws catchable TypeError (§20.3.3.3 / §21.1.3.7) ---

#[test]
fn wrapper_value_of_incompatible_receiver_throws_type_error() {
  assert_true(
    "let t=false; try { Number.prototype.valueOf.call({}); } catch (e) { t = e instanceof TypeError; } t",
  );
  assert_true(
    "let t=false; try { Boolean.prototype.valueOf.call({}); } catch (e) { t = e instanceof TypeError; } t",
  );
  // The boxed wrapper recovers its primitive.
  assert_true("Number.prototype.valueOf.call(new Number(7)) === 7");
  assert_true("Boolean.prototype.valueOf.call(new Boolean(true)) === true");
}

#[test]
fn array_is_array_and_rest_destructure() {
  // §23.1.2.2 + array rest BindingInitialization (`ArrayCreate`).
  assert_true("Array.isArray([]) === true");
  assert_true("Array.isArray({}) === false");
  assert_true("Array.isArray(null) === false");
  assert_true(
    "(() => { const [...x] = [1,2,3]; return Array.isArray(x) && x.length === 3 && x[0] === 1; })()",
  );
}

#[test]
fn number_prototype_data_and_formatting() {
  // §21.1.3 / §20.3.3: prototypes carry [[NumberData]]/+0 and [[BooleanData]]/false.
  assert_true("Number.prototype.toString() === '0'");
  assert_true("Boolean.prototype.toString() === 'false'");
  assert_true("Object.prototype.toString.call(Number.prototype) === '[object Number]'");
  assert_true("Object.prototype.toString.call(new Boolean(true)) === '[object Boolean]'");
  assert_true("(3).toExponential(0) === '3e+0'");
  assert_true("(100).toExponential() === '1e+2'");
  assert_true("(123.456).toExponential('2') === '1.23e+2'");
  assert_true("(123.456).toExponential([2]) === '1.23e+2'");
  assert_true("(123.456).toExponential(17) === '1.23456000000000003e+2'");
  assert_true("(123.456).toExponential(20) === '1.23456000000000003070e+2'");
  assert_true(
    "let t=false; try { NaN.toExponential({ valueOf() { throw new Error('vo'); } }); } catch (e) { t = e.message === 'vo'; } t",
  );
  assert_true("(3).toPrecision(1) === '3'");
  // Exact f64 for 1.2345e+27 is slightly below the decimal; p=4 must not round up.
  assert_true("(1.2345e+27).toPrecision(4) === '1.234e+27'");
  assert_true("(1.2345e+27).toPrecision(5) === '1.2345e+27'");
  // Exact f64 for 1e-21 is slightly below; high precision uses 9.999…e-22.
  assert_true("(1e-21).toPrecision(16) === '9.999999999999999e-22'");
  assert_true(
    "let t=false; try { (3).toFixed(101); } catch (e) { t = e instanceof RangeError; } t",
  );
  assert_true("'a.b'.split('.').length === 2 && 'a.b'.split('.')[0] === 'a'");
  assert_true("[2].toString() === '2'");
  assert_true("Number([2]) === 2");
}

#[test]
fn for_let_simple_inc() {
  assert_true("let s=0; for (let i=0; i<3; i++) { s+=i; } s===3");
}
#[test]
fn for_let_assign_inc() {
  assert_true("let s=0; for (let i=0; i<3; i=i+1) { s+=i; } s===3");
}
#[test]
fn for_let_single() {
  assert_true("let s=0; for (let radix=11; radix<=13; radix++) { s+=radix; } s===36");
}
#[test]
fn for_let_nested() {
  assert_true("let s=0; for (let radix=11; radix<=12; radix++) { for (let i=10; i<radix; i++) { s+=i; } } s===31");
}
#[test]
fn for_let_per_iteration_closure_capture() {
  // Each iteration body must capture a distinct `x` binding (CreatePerIterationEnvironment).
  assert_true(
    r#"
      var probeFirst;
      var probeSecond = null;
      for (let x = 'first'; probeSecond === null; x = 'second')
        if (!probeFirst)
          probeFirst = function() { return x; };
        else
          probeSecond = function() { return x; };
      probeFirst() === 'first' && probeSecond() === 'second'
    "#,
  );
}
#[test]
fn bigint_abstract_equality_with_string() {
  assert_true("0n == ''");
  assert_true("0n == '0'");
  assert_true("0n == '-0'");
  assert_true("!(0n == 'foo')");
  assert_true("1n == '1'");
  assert_true("16n == '0x10'");
  assert_true("0n == { toString() { return '0'; } }");
}
#[test]
fn compound_assignment_ops() {
  assert_true("let i=1; i*=2; i===2");
  assert_true("let i=16; i=i/2; i===8");
  assert_true("let i=2; i*=i; i===4");
  assert_true("let base=-3; (base **= 3) === -27 && base === -27");
  assert_true("let a=1; (a &&= 2) === 2 && a === 2");
  assert_true("let a=0; (a &&= 2) === 0 && a === 0");
  assert_true("let a=null; (a ??= 3) === 3 && a === 3");
}
#[test]
fn for_let_per_iteration_init_vs_body() {
  // Init closures see `loopEnv`; test/body/incr see the per-iteration env.
  assert_true(
    r#"
      var probeBefore, probeTest, probeIncr, probeBody;
      var run = true;
      for (
          let x = 'outside', _ = probeBefore = function() { return x; };
          run && (x = 'inside', probeTest = function() { return x; });
          probeIncr = function() { return x; }
        )
        probeBody = function() { return x; }, run = false;
      probeBefore() === 'outside'
        && probeTest() === 'inside'
        && probeBody() === 'inside'
        && probeIncr() === 'inside'
    "#,
  );
}

#[test]
fn if_and_for_completion_values() {
  assert_true("eval('1; if (true) { } else { }') === undefined");
  assert_true("eval('2; if (true) { 3; } else { }') === 3");
  assert_true("eval('4; if (true) { } else { 5; }') === undefined");
  assert_true("eval('1; if (true) { }') === undefined");
  assert_true("eval('for(;;){ 5; break; }') === 5");
  assert_true(
    "var supreme=5,count; eval('for(count=0;;) {if (count===supreme)break;else count++; }') === undefined",
  );
}
