package crud.springboot.service;

import java.util.List;

import crud.springboot.stubs.Employee;
import crud.springboot.stubs.Page;

/**
 * Service interface for Employee operations with JML specifications
 */
public interface EmployeeService {
    
    /**
     * Get all employees from the system
     * @return List of all employees (never null)
     */
    /*@ ensures \result != null;
      @*/
    List<Employee> getAllEmployees();
    
    /**
     * Save an employee to the system
     * @param employee The employee to save (must not be null)
     */
    /*@ requires employee != null;
      @*/
    void saveEmployee(Employee employee);
    
    /**
     * Get an employee by their ID
     * @param id The employee ID (must be positive)
     * @return The employee with given ID, or null if not found
     */
    /*@ requires id > 0;
      @ ensures (\result == null) || (\result.getId() == id);
      @*/
    Employee getEmployeeById(long id);
    
    /**
     * Delete an employee by their ID
     * @param id The employee ID to delete (must be positive)
     */
    /*@ requires id > 0;
      @*/
    void deleteEmployeeById(long id);
    
    /**
     * Find employees with pagination
     * @param pageNo Page number (must be positive)
     * @param pageSize Number of items per page (must be positive)
     * @param sortField Field to sort by (must not be null)
     * @param sortDirection Sort direction (must not be null)
     * @return Page of employees (never null)
     */
    /*@ requires pageNo > 0;
      @ requires pageSize > 0;
      @ requires sortField != null;
      @ requires sortDirection != null;
      @ ensures \result != null;
      @*/
    Page<Employee> findPaginated(int pageNo, int pageSize, String sortField, String sortDirection);
}