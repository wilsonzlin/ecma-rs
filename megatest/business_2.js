"use strict";

/**
 * ------------------------------
 * Type Hints (Comments Only)
 * ------------------------------
 *
 * @typedef {("PLACED" | "SHIPPED" | "DELIVERED")} OrderStatus
 * A string-literal enum for possible order states.
 *
 * @typedef {Object} Product
 * @property {string}  productId   - Unique product identifier
 * @property {string}  name        - Display name
 * @property {number}  unitPrice   - Price per item
 *
 * @typedef {Object} LineItem
 * @property {Product} product
 * @property {number}  quantity
 *
 * @typedef {Object} Order
 * @property {string}       orderId       - Unique order identifier
 * @property {string}       userId
 * @property {OrderStatus}  status
 * @property {number}       createdTime   - Unix timestamp
 * @property {number}       updateTime    - Unix timestamp
 * @property {LineItem[]}   lineItems
 * @property {number}       discount      - A discount in fractional form (e.g., 0.1 for 10%)
 * @property {boolean}      isPriority    - For demonstration: special handling logic
 */

/** “Enum” of order status, for clarity. */
const ORDER_STATUS = {
  PLACED: "PLACED",
  SHIPPED: "SHIPPED",
  DELIVERED: "DELIVERED",
};

/**
 * A small in-memory store for orders, to avoid dynamic reflection
 * or hidden classes from random property modifications.
 *
 * @type {Order[]}
 */
let allOrders = [];

/**
 * Create a new Order in an immutable style.
 * Returns a newly constructed `Order`.
 *
 * @param {string} userId
 * @returns {Order}
 */
const createOrder = (userId) => {
  const now = Date.now();
  return {
    orderId: generateUniqueOrderId(userId, now),
    userId,
    status: ORDER_STATUS.PLACED,
    createdTime: now,
    updateTime: now,
    lineItems: [],
    discount: 0.0, // no discount by default
    isPriority: false,
  };
};

/**
 * A helper to generate a unique (but simple) order ID.
 * @param {string} userId
 * @param {number} time
 * @returns {string}
 */
const generateUniqueOrderId = (userId, time) =>
  `${userId}-${time}-${Math.floor(Math.random() * 100000)}`;

/**
 * Add an order to the in-memory store. Returns the updated store array
 * (immutably).
 *
 * @param {Order[]} currentStore
 * @param {Order} newOrder
 * @returns {Order[]}
 */
const addOrderToStore = (currentStore, newOrder) => {
  // Return a new array with the new order appended.
  return [...currentStore, newOrder];
};

/**
 * Add a new line item to an existing order, returning a brand-new order object.
 *
 * @param {Order} order
 * @param {Product} product
 * @param {number} quantity
 * @returns {Order}
 */
const addLineItem = (order, product, quantity) => {
  const now = Date.now();
  const newItem = {
    product,
    quantity,
  };
  return {
    ...order,
    lineItems: [...order.lineItems, newItem],
    updateTime: now,
  };
};

/**
 * Update the discount on an order, immutably.
 *
 * @param {Order} order
 * @param {number} discount - Value in [0, 1], e.g. 0.1 for 10%
 * @returns {Order}
 */
const updateOrderDiscount = (order, discount) => {
  const now = Date.now();
  return {
    ...order,
    discount,
    updateTime: now,
  };
};

/**
 * Toggle the priority flag on an order, immutably.
 *
 * @param {Order} order
 * @returns {Order}
 */
const togglePriority = (order) => {
  const now = Date.now();
  return {
    ...order,
    isPriority: !order.isPriority,
    updateTime: now,
  };
};

/**
 * Update the status on an order, immutably.
 *
 * @param {Order} order
 * @param {OrderStatus} newStatus
 * @returns {Order}
 */
const updateOrderStatus = (order, newStatus) => {
  const now = Date.now();
  return {
    ...order,
    status: newStatus,
    updateTime: now,
  };
};

/**
 * Compute the total cost of an order. Demonstrates array `map`, `reduce`,
 * and numeric computations that can be inlined/optimized.
 *
 * @param {Order} order
 * @returns {number} total cost, post-discount
 */
const calculateOrderTotal = (order) => {
  let baseTotal = 0;
  for (let i = 0; i < order.lineItems.length; i++) {
    const item = order.lineItems[i];
    baseTotal += item.product.unitPrice * item.quantity;
  }

  // Apply discount if any
  if (order.discount > 0) {
    baseTotal = baseTotal * (1 - order.discount);
  }
  return baseTotal;
};

/**
 * Get all orders for a particular user, filtering from the global store.
 *
 * @param {Order[]} store
 * @param {string} userId
 * @returns {Order[]}
 */
const getOrdersByUser = (store, userId) => {
  /** @type {Order[]} */
  const userOrders = [];
  for (let i = 0; i < store.length; i++) {
    const o = store[i];
    if (o.userId === userId) {
      userOrders.push(o);
    }
  }
  return userOrders;
};

/**
 * Filter orders by status, demonstrating array iteration.
 *
 * @param {Order[]} store
 * @param {OrderStatus} status
 * @returns {Order[]}
 */
const getOrdersByStatus = (store, status) => {
  /** @type {Order[]} */
  const matched = [];
  for (let i = 0; i < store.length; i++) {
    const o = store[i];
    if (o.status === status) {
      matched.push(o);
    }
  }
  return matched;
};

/**
 * Example “Product database” — In real-world usage, these would
 * come from an external data source.
 *
 * @type {Product[]}
 */
const productsCatalog = [
  { productId: "SKU-001", name: "Pencil", unitPrice: 0.5 },
  { productId: "SKU-002", name: "Notebook", unitPrice: 2.0 },
  { productId: "SKU-003", name: "Backpack", unitPrice: 20.0 },
];

/**
 * Main demonstration function tying it all together.
 */
const main = () => {
  // 1) Create a new order for user “userA”
  let newOrder = createOrder("userA");

  // 2) Add line items to it (immutably)
  newOrder = addLineItem(newOrder, productsCatalog[0], 10); // 10 pencils
  newOrder = addLineItem(newOrder, productsCatalog[1], 5);  // 5 notebooks

  // 3) Mark it with a discount and priority
  newOrder = updateOrderDiscount(newOrder, 0.15); // 15% discount
  newOrder = togglePriority(newOrder);

  // 4) Add the order to our in-memory store
  allOrders = addOrderToStore(allOrders, newOrder);

  // 5) Create a second order for the same user, no discount
  let secondOrder = createOrder("userA");
  secondOrder = addLineItem(secondOrder, productsCatalog[2], 1); // 1 backpack
  allOrders = addOrderToStore(allOrders, secondOrder);

  // 6) “Ship” the first order
  const shippedOrder = updateOrderStatus(newOrder, ORDER_STATUS.SHIPPED);
  // Update the store in a real scenario, but we'll just log here
  console.log("Shipped order:", shippedOrder.orderId);

  // 7) Calculate totals for demonstration
  const firstOrderTotal = calculateOrderTotal(shippedOrder);
  const secondOrderTotal = calculateOrderTotal(secondOrder);
  console.log("First order total:", firstOrderTotal);
  console.log("Second order total:", secondOrderTotal);

  // 8) Query store for user “userA” (should see both orders)
  const userAOrders = getOrdersByUser(allOrders, "userA");
  console.log("Orders for userA:", userAOrders);

  // 9) Filter store for “PLACED” orders (should show the second order only)
  const placedOrders = getOrdersByStatus(allOrders, ORDER_STATUS.PLACED);
  console.log("All placed orders:", placedOrders);
};

main();
