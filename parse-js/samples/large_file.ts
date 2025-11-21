// Medium-sized TypeScript file (~300 lines)
// Domain: E-commerce application types

// Base types
type ID = string;
type Timestamp = number;
type Money = number;
type Email = string;
type URL = string;

// User types
interface User {
  id: ID;
  email: Email;
  firstName: string;
  lastName: string;
  createdAt: Timestamp;
  updatedAt: Timestamp;
  role: UserRole;
  profile: UserProfile;
  preferences: UserPreferences;
}

type UserRole = "customer" | "admin" | "moderator" | "vendor";

interface UserProfile {
  avatar?: URL;
  bio?: string;
  location?: string;
  phone?: string;
  dateOfBirth?: Timestamp;
}

interface UserPreferences {
  language: string;
  currency: string;
  notifications: NotificationPreferences;
  theme: "light" | "dark" | "auto";
}

interface NotificationPreferences {
  email: boolean;
  sms: boolean;
  push: boolean;
  marketing: boolean;
}

// Product types
interface Product {
  id: ID;
  sku: string;
  name: string;
  description: string;
  price: Money;
  salePrice?: Money;
  category: Category;
  tags: string[];
  images: ProductImage[];
  variants: ProductVariant[];
  inventory: InventoryStatus;
  createdAt: Timestamp;
  updatedAt: Timestamp;
}

interface Category {
  id: ID;
  name: string;
  slug: string;
  parent?: Category;
  children?: Category[];
}

interface ProductImage {
  url: URL;
  alt: string;
  width: number;
  height: number;
  isPrimary: boolean;
}

interface ProductVariant {
  id: ID;
  productId: ID;
  name: string;
  attributes: VariantAttribute[];
  price: Money;
  sku: string;
  inventory: number;
}

interface VariantAttribute {
  name: string;
  value: string;
}

type InventoryStatus = "in_stock" | "low_stock" | "out_of_stock" | "pre_order";

// Order types
interface Order {
  id: ID;
  orderNumber: string;
  customer: User;
  items: OrderItem[];
  subtotal: Money;
  tax: Money;
  shipping: Money;
  total: Money;
  status: OrderStatus;
  shippingAddress: Address;
  billingAddress: Address;
  payment: PaymentInfo;
  createdAt: Timestamp;
  updatedAt: Timestamp;
}

interface OrderItem {
  product: Product;
  variant?: ProductVariant;
  quantity: number;
  price: Money;
  total: Money;
}

type OrderStatus =
  | "pending"
  | "processing"
  | "shipped"
  | "delivered"
  | "cancelled"
  | "refunded";

interface Address {
  street1: string;
  street2?: string;
  city: string;
  state: string;
  postalCode: string;
  country: string;
}

interface PaymentInfo {
  method: PaymentMethod;
  status: PaymentStatus;
  transactionId?: string;
  last4?: string;
}

type PaymentMethod = "credit_card" | "debit_card" | "paypal" | "apple_pay" | "google_pay";
type PaymentStatus = "pending" | "authorized" | "captured" | "failed" | "refunded";

// Cart types
interface Cart {
  id: ID;
  userId?: ID;
  items: CartItem[];
  subtotal: Money;
  createdAt: Timestamp;
  updatedAt: Timestamp;
  expiresAt: Timestamp;
}

interface CartItem {
  productId: ID;
  variantId?: ID;
  quantity: number;
  price: Money;
}

// Review types
interface Review {
  id: ID;
  productId: ID;
  userId: ID;
  rating: 1 | 2 | 3 | 4 | 5;
  title: string;
  comment: string;
  helpful: number;
  notHelpful: number;
  verified: boolean;
  createdAt: Timestamp;
}

// Search and filter types
interface SearchQuery {
  q: string;
  category?: string;
  minPrice?: Money;
  maxPrice?: Money;
  tags?: string[];
  sort?: SortOption;
  page: number;
  limit: number;
}

type SortOption = "relevance" | "price_low" | "price_high" | "newest" | "rating";

interface SearchResult<T> {
  items: T[];
  total: number;
  page: number;
  limit: number;
  hasMore: boolean;
}

// API response types
interface APIResponse<T> {
  success: boolean;
  data?: T;
  error?: APIError;
  meta?: ResponseMeta;
}

interface APIError {
  code: string;
  message: string;
  details?: Record<string, any>;
}

interface ResponseMeta {
  requestId: string;
  timestamp: Timestamp;
  version: string;
}

// Event types
type UserEvent =
  | { type: "user.created"; data: User }
  | { type: "user.updated"; data: User }
  | { type: "user.deleted"; data: { id: ID } };

type OrderEvent =
  | { type: "order.created"; data: Order }
  | { type: "order.updated"; data: Order }
  | { type: "order.shipped"; data: { orderId: ID; trackingNumber: string } }
  | { type: "order.cancelled"; data: { orderId: ID; reason: string } };

type ProductEvent =
  | { type: "product.created"; data: Product }
  | { type: "product.updated"; data: Product }
  | { type: "product.deleted"; data: { id: ID } }
  | { type: "product.inventory_low"; data: { productId: ID; quantity: number } };

type AppEvent = UserEvent | OrderEvent | ProductEvent;

// Utility types
type EventType<E> = E extends { type: infer T } ? T : never;
type EventData<E, T> = E extends { type: T; data: infer D } ? D : never;

// Service interfaces
interface UserService {
  getUser(id: ID): Promise<User | null>;
  createUser(data: CreateUserData): Promise<User>;
  updateUser(id: ID, data: UpdateUserData): Promise<User>;
  deleteUser(id: ID): Promise<void>;
  listUsers(filter: UserFilter): Promise<SearchResult<User>>;
}

interface CreateUserData {
  email: Email;
  firstName: string;
  lastName: string;
  password: string;
}

interface UpdateUserData {
  firstName?: string;
  lastName?: string;
  profile?: Partial<UserProfile>;
  preferences?: Partial<UserPreferences>;
}

interface UserFilter {
  role?: UserRole;
  createdAfter?: Timestamp;
  createdBefore?: Timestamp;
  search?: string;
}

// Configuration types
interface AppConfig {
  api: APIConfig;
  payment: PaymentConfig;
  storage: StorageConfig;
  email: EmailConfig;
}

interface APIConfig {
  baseUrl: URL;
  timeout: number;
  retries: number;
  apiKey: string;
}

interface PaymentConfig {
  provider: "stripe" | "paypal" | "square";
  publicKey: string;
  secretKey: string;
  webhookSecret: string;
}

interface StorageConfig {
  provider: "s3" | "gcs" | "azure";
  bucket: string;
  region: string;
  credentials: StorageCredentials;
}

interface StorageCredentials {
  accessKeyId: string;
  secretAccessKey: string;
}

interface EmailConfig {
  provider: "sendgrid" | "mailgun" | "ses";
  apiKey: string;
  fromEmail: Email;
  fromName: string;
}
// Medium-sized TypeScript file (~300 lines)
// Domain: E-commerce application types

// Base types
type ID = string;
type Timestamp = number;
type Money = number;
type Email = string;
type URL = string;

// User types
interface User {
  id: ID;
  email: Email;
  firstName: string;
  lastName: string;
  createdAt: Timestamp;
  updatedAt: Timestamp;
  role: UserRole;
  profile: UserProfile;
  preferences: UserPreferences;
}

type UserRole = "customer" | "admin" | "moderator" | "vendor";

interface UserProfile {
  avatar?: URL;
  bio?: string;
  location?: string;
  phone?: string;
  dateOfBirth?: Timestamp;
}

interface UserPreferences {
  language: string;
  currency: string;
  notifications: NotificationPreferences;
  theme: "light" | "dark" | "auto";
}

interface NotificationPreferences {
  email: boolean;
  sms: boolean;
  push: boolean;
  marketing: boolean;
}

// Product types
interface Product {
  id: ID;
  sku: string;
  name: string;
  description: string;
  price: Money;
  salePrice?: Money;
  category: Category;
  tags: string[];
  images: ProductImage[];
  variants: ProductVariant[];
  inventory: InventoryStatus;
  createdAt: Timestamp;
  updatedAt: Timestamp;
}

interface Category {
  id: ID;
  name: string;
  slug: string;
  parent?: Category;
  children?: Category[];
}

interface ProductImage {
  url: URL;
  alt: string;
  width: number;
  height: number;
  isPrimary: boolean;
}

interface ProductVariant {
  id: ID;
  productId: ID;
  name: string;
  attributes: VariantAttribute[];
  price: Money;
  sku: string;
  inventory: number;
}

interface VariantAttribute {
  name: string;
  value: string;
}

type InventoryStatus = "in_stock" | "low_stock" | "out_of_stock" | "pre_order";

// Order types
interface Order {
  id: ID;
  orderNumber: string;
  customer: User;
  items: OrderItem[];
  subtotal: Money;
  tax: Money;
  shipping: Money;
  total: Money;
  status: OrderStatus;
  shippingAddress: Address;
  billingAddress: Address;
  payment: PaymentInfo;
  createdAt: Timestamp;
  updatedAt: Timestamp;
}

interface OrderItem {
  product: Product;
  variant?: ProductVariant;
  quantity: number;
  price: Money;
  total: Money;
}

type OrderStatus =
  | "pending"
  | "processing"
  | "shipped"
  | "delivered"
  | "cancelled"
  | "refunded";

interface Address {
  street1: string;
  street2?: string;
  city: string;
  state: string;
  postalCode: string;
  country: string;
}

interface PaymentInfo {
  method: PaymentMethod;
  status: PaymentStatus;
  transactionId?: string;
  last4?: string;
}

type PaymentMethod = "credit_card" | "debit_card" | "paypal" | "apple_pay" | "google_pay";
type PaymentStatus = "pending" | "authorized" | "captured" | "failed" | "refunded";

// Cart types
interface Cart {
  id: ID;
  userId?: ID;
  items: CartItem[];
  subtotal: Money;
  createdAt: Timestamp;
  updatedAt: Timestamp;
  expiresAt: Timestamp;
}

interface CartItem {
  productId: ID;
  variantId?: ID;
  quantity: number;
  price: Money;
}

// Review types
interface Review {
  id: ID;
  productId: ID;
  userId: ID;
  rating: 1 | 2 | 3 | 4 | 5;
  title: string;
  comment: string;
  helpful: number;
  notHelpful: number;
  verified: boolean;
  createdAt: Timestamp;
}

// Search and filter types
interface SearchQuery {
  q: string;
  category?: string;
  minPrice?: Money;
  maxPrice?: Money;
  tags?: string[];
  sort?: SortOption;
  page: number;
  limit: number;
}

type SortOption = "relevance" | "price_low" | "price_high" | "newest" | "rating";

interface SearchResult<T> {
  items: T[];
  total: number;
  page: number;
  limit: number;
  hasMore: boolean;
}

// API response types
interface APIResponse<T> {
  success: boolean;
  data?: T;
  error?: APIError;
  meta?: ResponseMeta;
}

interface APIError {
  code: string;
  message: string;
  details?: Record<string, any>;
}

interface ResponseMeta {
  requestId: string;
  timestamp: Timestamp;
  version: string;
}

// Event types
type UserEvent =
  | { type: "user.created"; data: User }
  | { type: "user.updated"; data: User }
  | { type: "user.deleted"; data: { id: ID } };

type OrderEvent =
  | { type: "order.created"; data: Order }
  | { type: "order.updated"; data: Order }
  | { type: "order.shipped"; data: { orderId: ID; trackingNumber: string } }
  | { type: "order.cancelled"; data: { orderId: ID; reason: string } };

type ProductEvent =
  | { type: "product.created"; data: Product }
  | { type: "product.updated"; data: Product }
  | { type: "product.deleted"; data: { id: ID } }
  | { type: "product.inventory_low"; data: { productId: ID; quantity: number } };

type AppEvent = UserEvent | OrderEvent | ProductEvent;

// Utility types
type EventType<E> = E extends { type: infer T } ? T : never;
type EventData<E, T> = E extends { type: T; data: infer D } ? D : never;

// Service interfaces
interface UserService {
  getUser(id: ID): Promise<User | null>;
  createUser(data: CreateUserData): Promise<User>;
  updateUser(id: ID, data: UpdateUserData): Promise<User>;
  deleteUser(id: ID): Promise<void>;
  listUsers(filter: UserFilter): Promise<SearchResult<User>>;
}

interface CreateUserData {
  email: Email;
  firstName: string;
  lastName: string;
  password: string;
}

interface UpdateUserData {
  firstName?: string;
  lastName?: string;
  profile?: Partial<UserProfile>;
  preferences?: Partial<UserPreferences>;
}

interface UserFilter {
  role?: UserRole;
  createdAfter?: Timestamp;
  createdBefore?: Timestamp;
  search?: string;
}

// Configuration types
interface AppConfig {
  api: APIConfig;
  payment: PaymentConfig;
  storage: StorageConfig;
  email: EmailConfig;
}

interface APIConfig {
  baseUrl: URL;
  timeout: number;
  retries: number;
  apiKey: string;
}

interface PaymentConfig {
  provider: "stripe" | "paypal" | "square";
  publicKey: string;
  secretKey: string;
  webhookSecret: string;
}

interface StorageConfig {
  provider: "s3" | "gcs" | "azure";
  bucket: string;
  region: string;
  credentials: StorageCredentials;
}

interface StorageCredentials {
  accessKeyId: string;
  secretAccessKey: string;
}

interface EmailConfig {
  provider: "sendgrid" | "mailgun" | "ses";
  apiKey: string;
  fromEmail: Email;
  fromName: string;
}
// Complex TypeScript type constructs

// Conditional types
type IsString<T> = T extends string ? true : false;
type Unwrap<T> = T extends Promise<infer U> ? U : T;
type ReturnType<T> = T extends (...args: any[]) => infer R ? R : never;

// Mapped types
type Readonly<T> = { readonly [P in keyof T]: T[P] };
type Partial<T> = { [P in keyof T]?: T[P] };
type Required<T> = { [P in keyof T]-?: T[P] };
type Nullable<T> = { [P in keyof T]: T[P] | null };

// Template literal types
type HTTPMethod = "GET" | "POST" | "PUT" | "DELETE";
type Endpoint = `/${string}`;
type Route = `${HTTPMethod} ${Endpoint}`;
type UppercaseHTTP = Uppercase<HTTPMethod>;
type LowercaseHTTP = Lowercase<HTTPMethod>;

// Recursive types
type JSONValue = string | number | boolean | null | JSONObject | JSONArray;
interface JSONObject {
  [key: string]: JSONValue;
}
interface JSONArray extends Array<JSONValue> {}

// Advanced conditional types
type Diff<T, U> = T extends U ? never : T;
type Filter<T, U> = T extends U ? T : never;
type NonNullable<T> = T extends null | undefined ? never : T;

// Distributive conditional types
type ToArray<T> = T extends any ? T[] : never;
type BoxedValue<T> = { value: T extends any ? T : never };

// Infer with nested conditionals
type UnpackArray<T> = T extends (infer U)[] ? U : T;
type UnpackPromise<T> = T extends Promise<infer U> ? U : T;
type DeepUnpack<T> = T extends Promise<infer U>
  ? DeepUnpack<U>
  : T extends (infer U)[]
    ? DeepUnpack<U>
    : T;

// Complex mapped types
type Getters<T> = {
  [K in keyof T as `get${Capitalize<string & K>}`]: () => T[K];
};

type Setters<T> = {
  [K in keyof T as `set${Capitalize<string & K>}`]: (value: T[K]) => void;
};

// Intersection types
type MixedType = { a: string } & { b: number } & { c: boolean };
type DeepMerge<T, U> = {
  [K in keyof T | keyof U]: K extends keyof T
    ? K extends keyof U
      ? T[K] | U[K]
      : T[K]
    : K extends keyof U
      ? U[K]
      : never;
};

// Variadic tuple types
type Concat<T extends any[], U extends any[]> = [...T, ...U];
type Tail<T extends any[]> = T extends [any, ...infer Rest] ? Rest : never;
type Head<T extends any[]> = T extends [infer First, ...any[]] ? First : never;

// Key remapping in mapped types
type EventHandlers<T> = {
  [K in keyof T as `on${Capitalize<string & K>}Change`]: (newValue: T[K]) => void;
};

// Conditional types with multiple infer
type ConstructorParams<T> = T extends new (...args: infer P) => any ? P : never;
type InstanceType<T> = T extends new (...args: any[]) => infer R ? R : any;

// Advanced template literal types
type CSSProperty = "width" | "height" | "color" | "backgroundColor";
type CSSValue = string | number;
type CSSProperties = {
  [K in CSSProperty]: CSSValue;
};

type DataAttribute = `data-${string}`;
type AriaAttribute = `aria-${string}`;

// Complex utility types
type DeepReadonly<T> = {
  readonly [P in keyof T]: T[P] extends object ? DeepReadonly<T[P]> : T[P];
};

type DeepPartial<T> = {
  [P in keyof T]?: T[P] extends object ? DeepPartial<T[P]> : T[P];
};

// Branded types
type Brand<K, T> = K & { __brand: T };
type USD = Brand<number, "USD">;
type EUR = Brand<number, "EUR">;

// Higher-order types
type Functor<F> = {
  map: <A, B>(f: (a: A) => B) => (fa: F) => F;
};

// Complex generic constraints
type KeysOfType<T, U> = {
  [K in keyof T]: T[K] extends U ? K : never;
}[keyof T];

type PickByType<T, U> = Pick<T, KeysOfType<T, U>>;
type OmitByType<T, U> = Omit<T, KeysOfType<T, U>>;

// Assertion functions
type AssertIsString<T> = T extends string ? T : never;
type AssertIsArray<T> = T extends any[] ? T : never;
// Simple interfaces and type aliases
interface User {
  id: number;
  name: string;
  email: string;
  age?: number;
  readonly createdAt: Date;
}

interface Post {
  id: number;
  title: string;
  content: string;
  author: User;
  tags: string[];
}

type UserRole = "admin" | "user" | "guest";

interface Admin extends User {
  role: "admin";
  permissions: string[];
}

interface Config {
  apiUrl: string;
  timeout: number;
  retries?: number;
}

// Function types
type Callback = (error: Error | null, data: any) => void;
type AsyncCallback = () => Promise<void>;

// Index signatures
interface Dictionary {
  [key: string]: string;
}

interface NumberDictionary {
  [index: number]: string;
}

// Generic interfaces
interface Container<T> {
  value: T;
  getValue(): T;
}

interface Pair<K, V> {
  key: K;
  value: V;
}
// Small file with primitive types
type StringType = string;
type NumberType = number;
type BooleanType = boolean;
type NullType = null;
type UndefinedType = undefined;
type VoidType = void;
type AnyType = any;
type UnknownType = unknown;
type NeverType = never;

// Literal types
type LiteralString = "hello";
type LiteralNumber = 42;
type LiteralBoolean = true;

// Simple unions
type StringOrNumber = string | number;
type Status = "active" | "inactive" | "pending";

// Simple arrays
type StringArray = string[];
type NumberArray = Array<number>;

// Basic tuples
type Point = [number, number];
type NamedTuple = [string, number];
