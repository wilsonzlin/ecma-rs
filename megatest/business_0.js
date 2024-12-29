// @ts-check

/** @typedef {"USD" | "EUR" | "GBP"} Currency */
/** @typedef {"PENDING" | "PROCESSING" | "SHIPPED" | "DELIVERED" | "CANCELLED"} OrderStatus */
/** @typedef {"FOOD" | "ELECTRONICS" | "CLOTHING"} ProductCategory */

/** @typedef {{
  id: string,
  name: string,
  price: Money,
  weight: number,
  category: ProductCategory,
  stockLevel: number,
  reorderPoint: number,
  supplierId: string
}} Product */

/** @typedef {{
  amount: number,
  currency: Currency
}} Money */

/** @typedef {{
  id: string,
  productId: string,
  quantity: number,
  priceAtTime: Money
}} OrderLine */

/** @typedef {{
  id: string,
  customerId: string,
  lines: OrderLine[],
  status: OrderStatus,
  created: number,
  lastUpdated: number,
  shippingAddress: Address,
  billingAddress: Address
}} Order */

/** @typedef {{
  street: string,
  city: string,
  country: string,
  postalCode: string
}} Address */

// Strongly typed Result type for error handling
class Result {
  /** @type {T | null} */ value;
  /** @type {string | null} */ error;

  /**
   * @template T
   * @param {T | null} value
   * @param {string | null} error
   */
  constructor(value, error) {
    this.value = value;
    this.error = error;
  }

  /**
   * @template T
   * @param {T} value
   * @returns {Result<T>}
   */
  static ok(value) {
    return new Result(value, null);
  }

  /**
   * @template T
   * @param {string} error
   * @returns {Result<T>}
   */
  static err(error) {
    return new Result(null, error);
  }

  /**
   * @template T, U
   * @param {(value: T) => U} fn
   * @returns {Result<U>}
   */
  map(fn) {
    if (this.error) return Result.err(this.error);
    return Result.ok(fn(this.value));
  }
}

// Fixed-shape class for money calculations with no dynamic properties
class MoneyCalc {
  /**
   * @param {Money} a
   * @param {Money} b
   * @returns {Result<Money>}
   */
  static add(a, b) {
    if (a.currency !== b.currency) {
      return Result.err(`Currency mismatch: ${a.currency} vs ${b.currency}`);
    }
    return Result.ok({
      amount: a.amount + b.amount,
      currency: a.currency
    });
  }

  /**
   * @param {Money} money
   * @param {number} quantity
   * @returns {Money}
   */
  static multiply(money, quantity) {
    return {
      amount: money.amount * quantity,
      currency: money.currency
    };
  }
}

// Inventory management with fixed struct shapes
class InventoryManager {
  /** @type {Map<string, Product>} */ products;
  /** @type {Map<string, Set<string>>} */ categoryIndex;

  constructor() {
    this.products = new Map();
    this.categoryIndex = new Map();
  }

  /**
   * @param {Product} product
   * @returns {Result<void>}
   */
  addProduct(product) {
    if (this.products.has(product.id)) {
      return Result.err(`Product ${product.id} already exists`);
    }

    this.products.set(product.id, product);

    if (!this.categoryIndex.has(product.category)) {
      this.categoryIndex.set(product.category, new Set());
    }
    this.categoryIndex.get(product.category).add(product.id);

    return Result.ok(undefined);
  }

  /**
   * @param {string} productId
   * @param {number} quantity
   * @returns {Result<void>}
   */
  reserveStock(productId, quantity) {
    const product = this.products.get(productId);
    if (!product) {
      return Result.err(`Product ${productId} not found`);
    }

    if (product.stockLevel < quantity) {
      return Result.err(`Insufficient stock for product ${productId}`);
    }

    product.stockLevel -= quantity;

    // Check reorder point
    if (product.stockLevel <= product.reorderPoint) {
      this.triggerReorder(product);
    }

    return Result.ok(undefined);
  }

  /**
   * @param {Product} product
   * @private
   */
  triggerReorder(product) {
    // In real system, would trigger reorder workflow
    console.log(`Reorder triggered for product ${product.id}`);
  }

  /**
   * @param {ProductCategory} category
   * @returns {Product[]}
   */
  getProductsByCategory(category) {
    const productIds = this.categoryIndex.get(category);
    if (!productIds) return [];

    return Array.from(productIds)
      .map(id => this.products.get(id))
      .filter(Boolean);
  }
}

// Order processing with explicit types and methods
class OrderProcessor {
  /** @type {InventoryManager} */ inventory;
  /** @type {Map<string, Order>} */ orders;

  /**
   * @param {InventoryManager} inventory
   */
  constructor(inventory) {
    this.inventory = inventory;
    this.orders = new Map();
  }

  /**
   * @param {Order} order
   * @returns {Result<Money>}
   */
  processOrder(order) {
    // Validate order
    const validationResult = this.validateOrder(order);
    if (validationResult.error) return validationResult;

    // Reserve inventory
    for (const line of order.lines) {
      const reserveResult = this.inventory.reserveStock(line.productId, line.quantity);
      if (reserveResult.error) {
        return Result.err(`Failed to reserve stock: ${reserveResult.error}`);
      }
    }

    // Calculate total
    let total = { amount: 0, currency: order.lines[0].priceAtTime.currency };
    for (const line of order.lines) {
      const lineTotal = MoneyCalc.multiply(line.priceAtTime, line.quantity);
      const addResult = MoneyCalc.add(total, lineTotal);
      if (addResult.error) return addResult;
      total = addResult.value;
    }

    // Update order status
    order.status = "PROCESSING";
    order.lastUpdated = Date.now();
    this.orders.set(order.id, order);

    return Result.ok(total);
  }

  /**
   * @param {Order} order
   * @returns {Result<void>}
   * @private
   */
  validateOrder(order) {
    if (!order.lines.length) {
      return Result.err("Order must contain at least one line");
    }

    const currency = order.lines[0].priceAtTime.currency;
    for (const line of order.lines) {
      if (line.priceAtTime.currency !== currency) {
        return Result.err("All order lines must use the same currency");
      }
      if (line.quantity <= 0) {
        return Result.err("Order line quantities must be positive");
      }
    }

    return Result.ok(undefined);
  }
}

// Example usage
function main() {
  const inventory = new InventoryManager();

  // Add products
  const laptop = {
    id: "LAPTOP-1",
    name: "High-End Laptop",
    price: { amount: 1299.99, currency: "USD" },
    weight: 2.1,
    category: "ELECTRONICS",
    stockLevel: 100,
    reorderPoint: 20,
    supplierId: "SUPP-1"
  };

  inventory.addProduct(laptop);

  // Create order processor
  const processor = new OrderProcessor(inventory);

  // Process order
  const order = {
    id: "ORDER-1",
    customerId: "CUST-1",
    lines: [{
      id: "LINE-1",
      productId: "LAPTOP-1",
      quantity: 2,
      priceAtTime: { amount: 1299.99, currency: "USD" }
    }],
    status: "PENDING",
    created: Date.now(),
    lastUpdated: Date.now(),
    shippingAddress: {
      street: "123 Main St",
      city: "Springfield",
      country: "US",
      postalCode: "12345"
    },
    billingAddress: {
      street: "123 Main St",
      city: "Springfield",
      country: "US",
      postalCode: "12345"
    }
  };

  const result = processor.processOrder(order);
  if (result.error) {
    console.error(`Order processing failed: ${result.error}`);
  } else {
    console.log(`Order processed successfully. Total: ${result.value.amount} ${result.value.currency}`);
  }
}

main();
