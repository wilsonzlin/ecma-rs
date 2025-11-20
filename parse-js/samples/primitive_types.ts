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
