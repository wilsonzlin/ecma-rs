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
