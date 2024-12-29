// Virtual DOM node representation
class VNode {
  constructor(type, props = {}, children = []) {
    this.type = type;
    this.props = props;
    this.children = children.flat(Infinity).filter(Boolean);
    this.key = props.key ?? null;
    this._domNode = null;
    this._component = null;
  }
}

// Component base class with lifecycle methods
class Component {
  #mounted = false;
  #vnode = null;
  #state = {};
  #updateQueue = [];
  #updateScheduled = false;

  constructor(props = {}) {
    this.props = new Proxy(props, {
      set: () => false,
      get: (target, key) => {
        this.#trackDependency('props', key);
        return target[key];
      }
    });
  }

  setState(updater) {
    this.#updateQueue.push(updater);
    this.#scheduleUpdate();
  }

  #scheduleUpdate() {
    if (this.#updateScheduled) return;
    this.#updateScheduled = true;
    queueMicrotask(() => {
      const nextState = { ...this.#state };

      for (const updater of this.#updateQueue) {
        Object.assign(
          nextState,
          typeof updater === 'function'
            ? updater(nextState)
            : updater
        );
      }

      this.#updateQueue = [];
      this.#updateScheduled = false;
      this.#state = nextState;

      if (this.#mounted) {
        this.#triggerUpdate();
      }
    });
  }

  #trackDependency(type, key) {
    // Dependency tracking could be implemented here
  }

  #triggerUpdate() {
    const oldVNode = this.#vnode;
    const newVNode = this.render();
    const patches = diff(oldVNode, newVNode);
    patch(oldVNode._domNode.parentNode, patches);
    this.#vnode = newVNode;
  }

  // Lifecycle methods
  componentDidMount() {}
  componentDidUpdate(prevProps, prevState) {}
  componentWillUnmount() {}
  shouldComponentUpdate(nextProps, nextState) { return true; }
  render() { return null; }
}

// Virtual DOM diffing algorithm
const diff = (oldVNode, newVNode) => {
  const patches = [];

  if (!oldVNode) {
    patches.push({ type: 'CREATE', vnode: newVNode });
  } else if (!newVNode) {
    patches.push({ type: 'REMOVE' });
  } else if (changed(oldVNode, newVNode)) {
    if (typeof oldVNode.type === 'function') {
      patches.push({
        type: 'COMPONENT_UPDATE',
        oldVNode,
        newVNode
      });
    } else {
      patches.push({ type: 'REPLACE', vnode: newVNode });
    }
  } else if (newVNode.type !== 'text') {
    const childPatches = diffChildren(
      oldVNode.children,
      newVNode.children
    );
    if (childPatches.length > 0) {
      patches.push({ type: 'CHILDREN', patches: childPatches });
    }

    const propPatches = diffProps(
      oldVNode.props,
      newVNode.props
    );
    if (Object.keys(propPatches).length > 0) {
      patches.push({ type: 'PROPS', patches: propPatches });
    }
  }

  return patches;
};

// Child reconciliation with keys
const diffChildren = (oldChildren, newChildren) => {
  const patches = [];
  const moves = [];

  // Build key-based maps
  const oldKeyMap = new Map();
  const newKeyMap = new Map();

  oldChildren.forEach((child, i) => {
    if (child.key != null) {
      oldKeyMap.set(child.key, i);
    }
  });

  newChildren.forEach((child, i) => {
    if (child.key != null) {
      newKeyMap.set(child.key, i);
    }
  });

  // Find moves for keyed elements
  oldKeyMap.forEach((oldIndex, key) => {
    if (newKeyMap.has(key)) {
      const newIndex = newKeyMap.get(key);
      if (oldIndex !== newIndex) {
        moves.push({
          type: 'MOVE',
          from: oldIndex,
          to: newIndex,
          key
        });
      }
    }
  });

  // Generate patches
  let currentPatch = [];
  const maxLen = Math.max(
    oldChildren.length,
    newChildren.length
  );

  for (let i = 0; i < maxLen; i++) {
    const oldChild = oldChildren[i];
    const newChild = newChildren[i];

    currentPatch = diff(oldChild, newChild);

    if (currentPatch.length > 0) {
      patches.push({
        index: i,
        patches: currentPatch
      });
    }
  }

  if (moves.length > 0) {
    patches.push({ type: 'REORDER', moves });
  }

  return patches;
};

// Props diffing
const diffProps = (oldProps, newProps) => {
  const patches = {};

  // Remove deleted props
  for (const key in oldProps) {
    if (!(key in newProps)) {
      patches[key] = undefined;
    }
  }

  // Set changed/new props
  for (const key in newProps) {
    if (oldProps[key] !== newProps[key]) {
      patches[key] = newProps[key];
    }
  }

  return patches;
};

// Check if vnode changed
const changed = (a, b) => {
  return typeof a.type !== typeof b.type ||
         typeof a.type === 'string' && a.type !== b.type ||
         a.key !== b.key ||
         hasChangedHooks(a, b);
};

// Hook change detection
const hasChangedHooks = (a, b) => {
  const hooksA = Object.entries(a.props)
    .filter(([k]) => k.startsWith('on'));
  const hooksB = Object.entries(b.props)
    .filter(([k]) => k.startsWith('on'));

  return hooksA.length !== hooksB.length ||
         hooksA.some(([k, v]) => b.props[k] !== v);
};

// DOM patching
const patch = (parent, patches, index = 0) => {
  if (!patches.length) return;

  const patch = patches[index];
  const el = parent.childNodes[index];

  switch (patch.type) {
    case 'CREATE': {
      const { vnode } = patch;
      const newEl = createElement(vnode);
      vnode._domNode = newEl;
      parent.appendChild(newEl);
      break;
    }
    case 'REMOVE': {
      parent.removeChild(el);
      break;
    }
    case 'REPLACE': {
      const { vnode } = patch;
      const newEl = createElement(vnode);
      vnode._domNode = newEl;
      parent.replaceChild(newEl, el);
      break;
    }
    case 'PROPS': {
      patchProps(el, patch.patches);
      break;
    }
    case 'CHILDREN': {
      patch.patches.forEach(p => {
        patch(el, [p], p.index);
      });
      break;
    }
    case 'COMPONENT_UPDATE': {
      const { oldVNode, newVNode } = patch;
      const component = oldVNode._component;

      if (component.shouldComponentUpdate(
        newVNode.props,
        component.state
      )) {
        const prevProps = component.props;
        component.props = newVNode.props;
        const vnode = component.render();
        const childPatches = diff(
          oldVNode._vnode,
          vnode
        );
        patch(el.parentNode, childPatches);
        component.componentDidUpdate(prevProps);
      }
      break;
    }
    case 'REORDER': {
      const { moves } = patch;
      const children = Array.from(parent.children);
      const keyMap = new Map();

      children.forEach((child, i) => {
        const key = child._vnode?.key;
        if (key != null) keyMap.set(key, child);
      });

      moves.forEach(({ from, to, key }) => {
        const child = keyMap.get(key);
        const refChild = children[to];
        parent.insertBefore(child, refChild);
      });
      break;
    }
  }
};

// Element creation
const createElement = (vnode) => {
  if (typeof vnode.type === 'function') {
    const component = new vnode.type(vnode.props);
    vnode._component = component;
    const renderedVNode = component.render();
    vnode._vnode = renderedVNode;
    const el = createElement(renderedVNode);
    component.componentDidMount();
    return el;
  }

  const el = vnode.type === 'text'
    ? document.createTextNode(vnode.props.nodeValue)
    : document.createElement(vnode.type);

  vnode._domNode = el;
  el._vnode = vnode;

  if (vnode.type !== 'text') {
    patchProps(el, vnode.props);
    vnode.children.forEach(child => {
      el.appendChild(createElement(child));
    });
  }

  return el;
};

// Props patching
const patchProps = (el, patches) => {
  for (const key in patches) {
    const value = patches[key];

    if (key.startsWith('on')) {
      const eventName = key.slice(2).toLowerCase();
      const oldHandler = el._handlers?.[eventName];

      if (oldHandler) {
        el.removeEventListener(eventName, oldHandler);
      }

      if (value) {
        el._handlers = el._handlers || {};
        el._handlers[eventName] = value;
        el.addEventListener(eventName, value);
      }
    } else if (key === 'style') {
      Object.assign(el.style, value);
    } else if (value === undefined) {
      el.removeAttribute(key);
    } else {
      el.setAttribute(key, value);
    }
  }
};

// Example usage
class Counter extends Component {
  state = { count: 0 };

  increment = () => {
    this.setState(state => ({
      count: state.count + 1
    }));
  };

  render() {
    const { count } = this.state;
    return new VNode('div', {},
      new VNode('text', { nodeValue: `Count: ${count}` }),
      new VNode('button', {
        onClick: this.increment
      }, [
        new VNode('text', { nodeValue: 'Increment' })
      ])
    );
  }
}

// Mount to DOM
const mount = (component, container) => {
  const vnode = new VNode(component);
  const dom = createElement(vnode);
  container.appendChild(dom);
  return vnode;
};
