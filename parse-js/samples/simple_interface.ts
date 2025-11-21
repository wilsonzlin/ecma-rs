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
