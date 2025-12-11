package crud.springboot.service;

import crud.springboot.model.Employee;
import crud.springboot.repository.EmployeeRepository;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import java.util.*;

import org.springframework.data.domain.*;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

class EmployeeServiceImplTest {

    @Mock
    private EmployeeRepository employeeRepository;

    @InjectMocks
    private EmployeeServiceImpl employeeService;

    @BeforeEach
    void setup() {
        MockitoAnnotations.openMocks(this);
    }

    @Test
    void testGetAllEmployees() {
        List<Employee> list = Arrays.asList(
                new Employee("A", "B", "a@b.com"),
                new Employee("C", "D", "c@d.com")
        );

        when(employeeRepository.findAll()).thenReturn(list);

        List<Employee> result = employeeService.getAllEmployees();
        assertThat(result).hasSize(2);
    }
    
    @Test
    void testSaveEmployee() {
        Employee e = new Employee("John", "Doe", "john@example.com");

        employeeService.saveEmployee(e);

        verify(employeeRepository, times(1)).save(e);
    }

    @Test
    void testGetEmployeeById() {
        Employee e = new Employee("A", "B", "a@b.com");

        when(employeeRepository.findById(1L)).thenReturn(Optional.of(e));

        Employee result = employeeService.getEmployeeById(1L);

        assertThat(result).isNotNull();
    }

    @Test
    void testDeleteEmployee() {
        employeeService.deleteEmployeeById(5L);

        verify(employeeRepository, times(1)).deleteById(5L);
    }

    @Test
    void testFindPaginated() {
        Page<Employee> page = new PageImpl<>(
                List.of(new Employee("A", "B", "a@b.com"))
        );

        when(employeeRepository.findAll(any(Pageable.class))).thenReturn(page);

        Page<Employee> result = employeeService.findPaginated(1, 5, "firstName", "asc");

        assertThat(result.getContent().size()).isEqualTo(1);
    }

    @Test
void testGetEmployeeById_NotFound() {
    when(employeeRepository.findById(1L)).thenReturn(Optional.empty());

    RuntimeException exception = assertThrows(RuntimeException.class,
            () -> employeeService.getEmployeeById(1L));

    assertThat(exception.getMessage()).contains("Employee not found");
}

@Test
void testFindPaginatedDescending() {
    Page<Employee> page = new PageImpl<>(List.of(new Employee("X", "Y", "x@y.com")));

    when(employeeRepository.findAll(any(Pageable.class)))
            .thenReturn(page);

    Page<Employee> result = employeeService.findPaginated(1, 5, "firstName", "desc");

    assertThat(result.getContent().size()).isEqualTo(1);
}

}
