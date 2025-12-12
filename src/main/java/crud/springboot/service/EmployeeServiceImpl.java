package crud.springboot.service.impl;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import org.springframework.data.domain.Page;
import org.springframework.data.domain.PageImpl;
import org.springframework.data.domain.PageRequest;
import org.springframework.stereotype.Service;

import crud.springboot.model.Employee;
import crud.springboot.service.EmployeeService;

/**
 * Implementation of EmployeeService
 * Converts stubs internally to model.Employee for controller
 */
@Service
public class EmployeeServiceImpl implements EmployeeService {

    // Internal stub repository (replace with actual stub source)
    private final List<crud.springboot.stubs.Employee> stubList = new ArrayList<>();

    // Helper method: convert stub to model.Employee
    private Employee convertToModel(crud.springboot.stubs.Employee stub) {
        Employee emp = new Employee();
        emp.setId(stub.getId());
        emp.setFirstName(stub.getFirstName());
        emp.setLastName(stub.getLastName());
        emp.setEmail(stub.getEmail());
        return emp;
    }

    @Override
    public List<Employee> getAllEmployees() {
        return stubList.stream()
                .map(this::convertToModel)
                .collect(Collectors.toList());
    }

    @Override
    public void saveEmployee(Employee employee) {
        // Convert model to stub before saving
        crud.springboot.stubs.Employee stub = new crud.springboot.stubs.Employee();
        stub.setId(employee.getId());
        stub.setFirstName(employee.getFirstName());
        stub.setLastName(employee.getLastName());
        stub.setEmail(employee.getEmail());
        stubList.add(stub);
    }

    @Override
    public Employee getEmployeeById(long id) {
        return stubList.stream()
                .filter(s -> s.getId() == id)
                .findFirst()
                .map(this::convertToModel)
                .orElse(null);
    }

    @Override
    public void deleteEmployeeById(long id) {
        stubList.removeIf(s -> s.getId() == id);
    }

    @Override
    public Page<Employee> findPaginated(int pageNo, int pageSize, String sortField, String sortDirection) {
        // Convert stubs to model
        List<Employee> modelList = stubList.stream()
                .map(this::convertToModel)
                .collect(Collectors.toList());

        // Pagination calculation
        int start = (pageNo - 1) * pageSize;
        int end = Math.min(start + pageSize, modelList.size());
        List<Employee> pageContent = start >= modelList.size() ? new ArrayList<>() : modelList.subList(start, end);

        return new PageImpl<>(pageContent, PageRequest.of(pageNo - 1, pageSize), modelList.size());
    }
}
