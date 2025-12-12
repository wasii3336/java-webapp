package crud.springboot.service.impl;

import crud.springboot.model.Employee;
import crud.springboot.repository.EmployeeRepository;
import crud.springboot.service.EmployeeService;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.data.domain.*;
import org.springframework.stereotype.Service;

import java.util.List;

@Service
public class EmployeeServiceImpl implements EmployeeService {

    @Autowired
    private EmployeeRepository employeeRepository;

    @Override
    public List<Employee> getAllEmployees() {
        return employeeRepository.findAll();
    }

    @Override
    public void saveEmployee(Employee employee) {
        // Interface requires void, so just save and ignore returned value
        employeeRepository.save(employee);
    }

@Override
public Employee getEmployeeById(long id) {
    return employeeRepository.findById(id)
            .orElseThrow(() -> new RuntimeException("Employee not found"));
}


    @Override
    public void deleteEmployeeById(long id) {
        employeeRepository.deleteById(id);
    }

    @Override
    public Page<Employee> findPaginated(int pageNo, int pageSize, String sortField, String sortDirection) {

        Sort sort = sortDirection.equalsIgnoreCase("asc") ?
                Sort.by(sortField).ascending() :
                Sort.by(sortField).descending();

        Pageable pageable = PageRequest.of(pageNo - 1, pageSize, sort);

        return employeeRepository.findAll(pageable);
    }
}
