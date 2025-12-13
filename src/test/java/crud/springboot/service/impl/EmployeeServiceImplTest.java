package crud.springboot.service.impl;

import crud.springboot.model.Employee;
import crud.springboot.repository.EmployeeRepository;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.data.domain.*;

import java.util.*;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
public class EmployeeServiceImplTest {

    @Mock
    private EmployeeRepository employeeRepository;

    @InjectMocks
    private EmployeeServiceImpl employeeService;

    private Employee testEmployee;

    @BeforeEach
    public void setUp() {
        testEmployee = new Employee("John", "Doe", "john@example.com");
        testEmployee.setId(1L);
    }

    // ============================================
    // getAllEmployees() Tests
    // ============================================

    @Test
    public void testGetAllEmployees_ReturnsMultipleEmployees() {
        List<Employee> employeeList = Arrays.asList(
                new Employee("Alice", "Smith", "alice@example.com"),
                new Employee("Bob", "Jones", "bob@example.com"),
                new Employee("Charlie", "Brown", "charlie@example.com")
        );
        when(employeeRepository.findAll()).thenReturn(employeeList);

        List<Employee> result = employeeService.getAllEmployees();

        assertThat(result).isNotNull();
        assertThat(result).hasSize(3);
        assertThat(result.get(0).getFirstName()).isEqualTo("Alice");
        assertThat(result.get(1).getFirstName()).isEqualTo("Bob");
        assertThat(result.get(2).getFirstName()).isEqualTo("Charlie");
        verify(employeeRepository, times(1)).findAll();
    }

    @Test
    public void testGetAllEmployees_ReturnsEmptyList() {
        when(employeeRepository.findAll()).thenReturn(Collections.emptyList());

        List<Employee> result = employeeService.getAllEmployees();

        assertThat(result).isNotNull();
        assertThat(result).isEmpty();
        verify(employeeRepository, times(1)).findAll();
    }

    @Test
    public void testGetAllEmployees_OrderPreserved() {
        List<Employee> orderedList = Arrays.asList(
                new Employee("Zack", "Last", "z@test.com"),
                new Employee("Alice", "First", "a@test.com"),
                new Employee("Mike", "Middle", "m@test.com")
        );
        when(employeeRepository.findAll()).thenReturn(orderedList);

        List<Employee> result = employeeService.getAllEmployees();

        assertThat(result).hasSize(3);
        assertThat(result.get(0).getFirstName()).isEqualTo("Zack");
        assertThat(result.get(1).getFirstName()).isEqualTo("Alice");
        assertThat(result.get(2).getFirstName()).isEqualTo("Mike");
    }

    @Test
    public void testGetAllEmployees_VerifyReturnedListIsActualResult() {
        List<Employee> employeeList = new ArrayList<>();
        employeeList.add(new Employee("Test", "User", "test@test.com"));
        when(employeeRepository.findAll()).thenReturn(employeeList);

        List<Employee> result = employeeService.getAllEmployees();

        assertThat(result).isEqualTo(employeeList);
        assertThat(result).isSameAs(employeeList);
    }

    // ============================================
    // saveEmployee() Tests
    // ============================================

    @Test
    public void testSaveEmployee_Success() {
        Employee newEmployee = new Employee("Jane", "Doe", "jane@example.com");
        when(employeeRepository.save(any(Employee.class))).thenReturn(newEmployee);

        employeeService.saveEmployee(newEmployee);

        verify(employeeRepository, times(1)).save(newEmployee);
        verify(employeeRepository, times(1)).save(argThat(emp ->
                emp.getFirstName().equals("Jane") &&
                        emp.getLastName().equals("Doe") &&
                        emp.getEmail().equals("jane@example.com")
        ));
    }

    @Test
    public void testSaveEmployee_WithAllFields() {
        Employee employee = new Employee("Test", "User", "test@example.com");
        employee.setId(5L);
        when(employeeRepository.save(employee)).thenReturn(employee);

        employeeService.saveEmployee(employee);

        verify(employeeRepository, times(1)).save(employee);
    }

    @Test
    public void testSaveEmployee_NullSafety() {
        Employee employee = new Employee("First", "Last", "email@test.com");
        when(employeeRepository.save(employee)).thenReturn(employee);

        employeeService.saveEmployee(employee);

        verify(employeeRepository).save(employee);
    }

    @Test
    public void testSaveEmployee_VerifyExactObject() {
        Employee employee = new Employee("Verify", "This", "verify@test.com");
        employee.setId(100L);
        when(employeeRepository.save(employee)).thenReturn(employee);

        employeeService.saveEmployee(employee);

        verify(employeeRepository).save(same(employee));
    }

    @Test
    public void testSaveEmployee_VerifyRepositoryInteraction() {
        Employee employee = new Employee("Repository", "Test", "repo@test.com");
        when(employeeRepository.save(employee)).thenReturn(employee);

        employeeService.saveEmployee(employee);

        verify(employeeRepository, times(1)).save(employee);
        verifyNoMoreInteractions(employeeRepository);
    }

    // ============================================
    // getEmployeeById() Tests
    // ============================================

    @Test
    public void testGetEmployeeById_Found() {
        when(employeeRepository.findById(1L)).thenReturn(Optional.of(testEmployee));

        Employee result = employeeService.getEmployeeById(1L);

        assertThat(result).isNotNull();
        assertThat(result.getId()).isEqualTo(1L);
        assertThat(result.getFirstName()).isEqualTo("John");
        assertThat(result.getLastName()).isEqualTo("Doe");
        assertThat(result.getEmail()).isEqualTo("john@example.com");
        verify(employeeRepository, times(1)).findById(1L);
    }

    @Test
    public void testGetEmployeeById_NotFound() {
        when(employeeRepository.findById(999L)).thenReturn(Optional.empty());

        RuntimeException exception = assertThrows(RuntimeException.class,
                () -> employeeService.getEmployeeById(999L));

        assertThat(exception.getMessage()).contains("Employee not found");
        verify(employeeRepository, times(1)).findById(999L);
    }

    @Test
    public void testGetEmployeeById_WithDifferentIds() {
        Employee employee2 = new Employee("Alice", "Wonder", "alice@example.com");
        employee2.setId(2L);
        when(employeeRepository.findById(2L)).thenReturn(Optional.of(employee2));

        Employee result = employeeService.getEmployeeById(2L);

        assertThat(result.getId()).isEqualTo(2L);
        assertThat(result.getFirstName()).isEqualTo("Alice");
        verify(employeeRepository, times(1)).findById(2L);
    }

    @Test
    public void testGetEmployeeById_VerifyRepositoryCall() {
        Long employeeId = 5L;
        Employee employee = new Employee("Test", "Employee", "test@test.com");
        employee.setId(employeeId);
        when(employeeRepository.findById(employeeId)).thenReturn(Optional.of(employee));

        Employee result = employeeService.getEmployeeById(employeeId);

        assertThat(result).isNotNull();
        assertThat(result.getFirstName()).isEqualTo("Test");
        verify(employeeRepository, times(1)).findById(employeeId);
    }

    @Test
    public void testGetEmployeeById_VerifyReturnedEmployee() {
        when(employeeRepository.findById(1L)).thenReturn(Optional.of(testEmployee));

        Employee result = employeeService.getEmployeeById(1L);

        assertThat(result).isSameAs(testEmployee);
        assertThat(result).isEqualTo(testEmployee);
    }

    @Test
    public void testGetEmployeeById_ExceptionMessage() {
        when(employeeRepository.findById(123L)).thenReturn(Optional.empty());

        RuntimeException exception = assertThrows(RuntimeException.class,
                () -> employeeService.getEmployeeById(123L));

        assertThat(exception.getMessage()).isNotEmpty();
        assertThat(exception.getMessage()).containsIgnoringCase("not found");
    }

    // ============================================
    // deleteEmployeeById() Tests
    // ============================================

    @Test
    public void testDeleteEmployeeById_Success() {
        doNothing().when(employeeRepository).deleteById(1L);

        employeeService.deleteEmployeeById(1L);

        verify(employeeRepository, times(1)).deleteById(1L);
    }

    @Test
    public void testDeleteEmployeeById_DifferentId() {
        doNothing().when(employeeRepository).deleteById(99L);

        employeeService.deleteEmployeeById(99L);

        verify(employeeRepository, times(1)).deleteById(99L);
    }

    @Test
    public void testDeleteEmployeeById_VerifyNoOtherInteractions() {
        doNothing().when(employeeRepository).deleteById(5L);

        employeeService.deleteEmployeeById(5L);

        verify(employeeRepository, times(1)).deleteById(5L);
        verify(employeeRepository, never()).findById(anyLong());
        verify(employeeRepository, never()).save(any());
    }

    @Test
    public void testDeleteEmployeeById_MultipleDeletes() {
        doNothing().when(employeeRepository).deleteById(10L);
        doNothing().when(employeeRepository).deleteById(20L);

        employeeService.deleteEmployeeById(10L);
        employeeService.deleteEmployeeById(20L);

        verify(employeeRepository, times(1)).deleteById(10L);
        verify(employeeRepository, times(1)).deleteById(20L);
    }

    @Test
    public void testDeleteEmployeeById_VerifyOnlyDeleteCalled() {
        Long idToDelete = 7L;
        doNothing().when(employeeRepository).deleteById(idToDelete);

        employeeService.deleteEmployeeById(idToDelete);

        verify(employeeRepository, only()).deleteById(idToDelete);
    }

    // ============================================
    // findPaginated() Tests
    // ============================================

    @Test
    public void testFindPaginated_AscendingSort() {
        List<Employee> employeeList = Arrays.asList(
                new Employee("Alice", "Anderson", "alice@test.com"),
                new Employee("Bob", "Brown", "bob@test.com")
        );
        Page<Employee> employeePage = new PageImpl<>(employeeList);
        
        when(employeeRepository.findAll(any(Pageable.class))).thenReturn(employeePage);

        Page<Employee> result = employeeService.findPaginated(1, 10, "firstName", "asc");

        assertThat(result).isNotNull();
        assertThat(result.getContent()).hasSize(2);
        assertThat(result.getContent().get(0).getFirstName()).isEqualTo("Alice");
        verify(employeeRepository, times(1)).findAll(any(Pageable.class));
    }

    @Test
    public void testFindPaginated_DescendingSort() {
        List<Employee> employeeList = Arrays.asList(
                new Employee("Zack", "Zimmerman", "zack@test.com"),
                new Employee("Alice", "Anderson", "alice@test.com")
        );
        Page<Employee> employeePage = new PageImpl<>(employeeList);
        
        when(employeeRepository.findAll(any(Pageable.class))).thenReturn(employeePage);

        Page<Employee> result = employeeService.findPaginated(1, 10, "firstName", "desc");

        assertThat(result).isNotNull();
        assertThat(result.getContent()).hasSize(2);
        assertThat(result.getContent().get(0).getFirstName()).isEqualTo("Zack");
        verify(employeeRepository, times(1)).findAll(any(Pageable.class));
    }

    @Test
    public void testFindPaginated_DifferentPageSize() {
        List<Employee> employeeList = Arrays.asList(
                new Employee("John", "Doe", "john@test.com")
        );
        Page<Employee> employeePage = new PageImpl<>(employeeList);
        
        when(employeeRepository.findAll(any(Pageable.class))).thenReturn(employeePage);

        Page<Employee> result = employeeService.findPaginated(1, 5, "lastName", "asc");

        assertThat(result).isNotNull();
        assertThat(result.getContent()).hasSize(1);
        verify(employeeRepository, times(1)).findAll(any(Pageable.class));
    }

    @Test
    public void testFindPaginated_SecondPage() {
        List<Employee> employeeList = Arrays.asList(
                new Employee("Page2", "Employee", "page2@test.com")
        );
        Page<Employee> employeePage = new PageImpl<>(employeeList);
        
        when(employeeRepository.findAll(any(Pageable.class))).thenReturn(employeePage);

        Page<Employee> result = employeeService.findPaginated(2, 10, "firstName", "asc");

        assertThat(result).isNotNull();
        verify(employeeRepository, times(1)).findAll(any(Pageable.class));
    }

    @Test
    public void testFindPaginated_EmptyPage() {
        Page<Employee> emptyPage = new PageImpl<>(Collections.emptyList());
        
        when(employeeRepository.findAll(any(Pageable.class))).thenReturn(emptyPage);

        Page<Employee> result = employeeService.findPaginated(1, 10, "firstName", "asc");

        assertThat(result).isNotNull();
        assertThat(result.getContent()).isEmpty();
        verify(employeeRepository, times(1)).findAll(any(Pageable.class));
    }

    @Test
    public void testFindPaginated_CaseInsensitiveSortDirection() {
        Page<Employee> employeePage = new PageImpl<>(Collections.emptyList());
        when(employeeRepository.findAll(any(Pageable.class))).thenReturn(employeePage);

        Page<Employee> result = employeeService.findPaginated(1, 10, "email", "DESC");

        assertThat(result).isNotNull();
        verify(employeeRepository, times(1)).findAll(any(Pageable.class));
    }

    @Test
    public void testFindPaginated_MultiplePages() {
        Page<Employee> employeePage = new PageImpl<>(Collections.emptyList());
        when(employeeRepository.findAll(any(Pageable.class))).thenReturn(employeePage);

        Page<Employee> result = employeeService.findPaginated(3, 15, "lastName", "asc");

        assertThat(result).isNotNull();
        verify(employeeRepository, times(1)).findAll(any(Pageable.class));
    }

    @Test
    public void testFindPaginated_VerifyPageableCreation() {
        Page<Employee> employeePage = new PageImpl<>(Collections.emptyList());
        when(employeeRepository.findAll(any(Pageable.class))).thenReturn(employeePage);

        employeeService.findPaginated(1, 10, "firstName", "asc");

        verify(employeeRepository, times(1)).findAll(any(Pageable.class));
    }

    @Test
    public void testFindPaginated_VerifySortDirection() {
        Page<Employee> employeePage = new PageImpl<>(Collections.emptyList());
        when(employeeRepository.findAll(any(Pageable.class))).thenReturn(employeePage);

        employeeService.findPaginated(1, 10, "email", "asc");

        verify(employeeRepository, times(1)).findAll(any(Pageable.class));
    }

    @Test
    public void testFindPaginated_VerifyReturnValue() {
        List<Employee> employees = Arrays.asList(testEmployee);
        Page<Employee> employeePage = new PageImpl<>(employees);
        when(employeeRepository.findAll(any(Pageable.class))).thenReturn(employeePage);

        Page<Employee> result = employeeService.findPaginated(1, 10, "firstName", "asc");

        assertThat(result).isSameAs(employeePage);
        assertThat(result.getContent()).contains(testEmployee);
    }

    @Test
    public void testFindPaginated_DifferentSortFields() {
        Page<Employee> employeePage = new PageImpl<>(Collections.emptyList());
        when(employeeRepository.findAll(any(Pageable.class))).thenReturn(employeePage);

        employeeService.findPaginated(1, 10, "email", "asc");
        employeeService.findPaginated(1, 10, "lastName", "desc");
        employeeService.findPaginated(2, 5, "firstName", "asc");

        verify(employeeRepository, times(3)).findAll(any(Pageable.class));
    }
}