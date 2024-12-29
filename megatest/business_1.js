"use strict";

/**
 * ------------------------------
 * Type Hints (Comments Only)
 * ------------------------------
 *
 * @typedef {"ENGINEERING" | "MARKETING" | "SALES" | "HR"} DepartmentType
 *
 * @typedef {"INTERN" | "REGULAR" | "SENIOR" | "LEAD"} RoleType
 *
 * @typedef {Object} EmployeeRecord
 * @property {string}      firstName
 * @property {string}      lastName
 * @property {DepartmentType} department
 * @property {RoleType}    role
 * @property {number}      salary       - Base salary
 * @property {boolean}     isActive     - If false, no longer employed
 *
 * @typedef {Object} PayrollResult
 * @property {string} employeeName
 * @property {number} grossPay
 * @property {number} taxAmount
 * @property {number} netPay
 */

/**
 * A static "enum" of tax rates by department for demonstration.
 * In a real scenario, this might come from a config or database.
 *
 * @type {{[key in DepartmentType]: number}}
 */
const DEPARTMENT_TAX_RATES = {
  ENGINEERING: 0.25,
  MARKETING: 0.23,
  SALES: 0.28,
  HR: 0.20,
};

/**
 * A static "enum" for roles and some contrived bonus multipliers.
 *
 * @type {{[key in RoleType]: number}}
 */
const ROLE_BONUS_MULTIPLIERS = {
  INTERN: 1.0,
  REGULAR: 1.05,
  SENIOR: 1.15,
  LEAD: 1.25,
};

/**
 * A utility function to create an EmployeeRecord with stable structure.
 *
 * @param {string} firstName
 * @param {string} lastName
 * @param {DepartmentType} department
 * @param {RoleType} role
 * @param {number} salary
 * @returns {EmployeeRecord}
 */
function createEmployee(firstName, lastName, department, role, salary) {
  return {
    firstName,
    lastName,
    department,
    role,
    salary,
    isActive: true,
  };
}

/**
 * An “object-oriented” style class with stable shape for storing and managing Employees.
 */
class Company {
  constructor() {
    /**
     * @type {EmployeeRecord[]}
     */
    this.employees = [];
  }

  /**
   * Add an EmployeeRecord to the company’s employee list.
   * @param {EmployeeRecord} employee
   */
  addEmployee(employee) {
    this.employees.push(employee);
  }

  /**
   * Mark an employee inactive by name, just to demonstrate stable lookups.
   * @param {string} firstName
   * @param {string} lastName
   */
  removeEmployeeByName(firstName, lastName) {
    for (let i = 0; i < this.employees.length; i++) {
      const emp = this.employees[i];
      if (emp.firstName === firstName && emp.lastName === lastName) {
        emp.isActive = false;
        return;
      }
    }
  }

  /**
   * Return the list of active employees in a given department.
   * @param {DepartmentType} department
   * @returns {EmployeeRecord[]}
   */
  getActiveEmployeesByDepartment(department) {
    /** @type {EmployeeRecord[]} */
    const results = [];
    for (let i = 0; i < this.employees.length; i++) {
      const emp = this.employees[i];
      if (emp.isActive && emp.department === department) {
        results.push(emp);
      }
    }
    return results;
  }

  /**
   * Generate a payroll report for all active employees.
   *
   * @returns {PayrollResult[]}
   */
  generatePayroll() {
    const payrollResults = [];
    for (let i = 0; i < this.employees.length; i++) {
      const emp = this.employees[i];
      if (!emp.isActive) {
        continue;
      }
      const result = calculatePayrollForEmployee(emp);
      payrollResults.push(result);
    }
    return payrollResults;
  }
}

/**
 * Calculate payroll for a single employee with stable logic.
 *
 * @param {EmployeeRecord} employee
 * @returns {PayrollResult}
 */
function calculatePayrollForEmployee(employee) {
  // Base salary adjusted by role
  const bonusMultiplier = ROLE_BONUS_MULTIPLIERS[employee.role] || 1.0;
  const grossPay = employee.salary * bonusMultiplier;

  // Tax is determined by department
  const taxRate = DEPARTMENT_TAX_RATES[employee.department] || 0.25;
  const taxAmount = grossPay * taxRate;

  return {
    employeeName: `${employee.firstName} ${employee.lastName}`,
    grossPay: grossPay,
    taxAmount: taxAmount,
    netPay: grossPay - taxAmount,
  };
}

/**
 * A small demonstration of how this code might be used in "business logic."
 */
function main() {
  const company = new Company();

  // Create some employees
  const e1 = createEmployee("Alice", "Anderson", "ENGINEERING", "REGULAR", 60000);
  const e2 = createEmployee("Bob", "Brown", "MARKETING", "SENIOR", 75000);
  const e3 = createEmployee("Charlie", "Clark", "SALES", "LEAD", 90000);
  const e4 = createEmployee("Diana", "Daniels", "ENGINEERING", "INTERN", 35000);

  // Add employees
  company.addEmployee(e1);
  company.addEmployee(e2);
  company.addEmployee(e3);
  company.addEmployee(e4);

  // Remove one employee
  company.removeEmployeeByName("Diana", "Daniels");

  // List active employees in Engineering
  const engEmployees = company.getActiveEmployeesByDepartment("ENGINEERING");
  console.log("Active Engineering Employees:");
  engEmployees.forEach((emp) => {
    console.log(emp.firstName, emp.lastName);
  });

  // Generate entire payroll
  const payroll = company.generatePayroll();
  console.log("Payroll Results:", payroll);
}

// Execute main to run the demonstration
main();
