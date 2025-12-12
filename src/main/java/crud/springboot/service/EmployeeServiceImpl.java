package crud.springboot.service;

import java.util.ArrayList;
import java.util.List;

import crud.springboot.stubs.Employee;
import crud.springboot.stubs.Page;

/**
 * Implementation of EmployeeService with JML specifications
 * This class provides in-memory storage and operations for Employee objects
 */
public class EmployeeServiceImpl implements EmployeeService {

    /**
     * In-memory list to store employees
     * spec_public allows this private field to be used in JML specifications
     */
    /*@ spec_public @*/ private List<Employee> employeeList = new ArrayList<Employee>();

    /**
     * Get all employees from the system
     * @return List of all employees (never null, returns the internal list)
     */
    //@ also
    /*@ ensures \result != null;
      @ ensures \result == employeeList;
      @*/
    public List<Employee> getAllEmployees() {
        return employeeList;
    }

    /**
     * Save an employee to the system
     * Adds the employee to the internal list
     * @param employee The employee to save (must not be null)
     */
    //@ also
    /*@ requires employee != null;
      @ ensures employeeList.contains(employee);
      @ ensures employeeList.size() == \old(employeeList.size()) + 1;
      @*/
    public void saveEmployee(Employee employee) {
        employeeList.add(employee);
    }

    /**
     * Get an employee by their ID
     * Searches through the list to find employee with matching ID
     * @param id The employee ID (must be positive)
     * @return The employee with given ID, or null if not found
     */
    //@ also
    /*@ requires id > 0;
      @ ensures (\result != null) ==> (\result.getId() == id);
      @ ensures (\result == null) ==> (\forall int i; 0 <= i && i < employeeList.size(); employeeList.get(i).getId() != id);
      @*/
    public Employee getEmployeeById(long id) {
        for (Employee emp : employeeList) {
            if (emp.getId() == id) {
                return emp;
            }
        }
        return null;
    }

    /**
     * Delete an employee by their ID
     * Removes the employee from the internal list
     * @param id The employee ID to delete (must be positive)
     */
    //@ also
    /*@ requires id > 0;
      @ ensures employeeList.size() <= \old(employeeList.size());
      @*/
    public void deleteEmployeeById(long id) {
        employeeList.removeIf(emp -> emp.getId() == id);
    }

    /**
     * Find employees with pagination
     * Returns a subset of employees based on page number and size
     * @param pageNo Page number (must be positive, 1-indexed)
     * @param pageSize Number of items per page (must be positive)
     * @param sortField Field to sort by (not used in this implementation)
     * @param sortDirection Sort direction (not used in this implementation)
     * @return Page containing the requested subset of employees
     */
    //@ also
    /*@ requires pageNo > 0;
      @ requires pageSize > 0;
      @ requires sortField != null;
      @ requires sortDirection != null;
      @ ensures \result != null;
      @*/
    public Page<Employee> findPaginated(int pageNo, int pageSize, String sortField, String sortDirection) {
        // Calculate start and end indices for pagination
        int start = (pageNo - 1) * pageSize;
        int end = Math.min(start + pageSize, employeeList.size());
        
        // Handle edge case where start index is beyond list size
        if (start >= employeeList.size()) {
            return new Page<Employee>(new ArrayList<Employee>());
        }
        
        // Get sublist and create page object
        List<Employee> content = new ArrayList<Employee>(employeeList.subList(start, end));
        return new Page<Employee>(content);
    }
}
