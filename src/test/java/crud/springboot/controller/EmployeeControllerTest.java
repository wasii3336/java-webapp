package crud.springboot.controller;

import crud.springboot.model.Employee;
import crud.springboot.service.EmployeeService;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.data.domain.Page;
import org.springframework.data.domain.PageImpl;
import org.springframework.ui.Model;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
public class EmployeeControllerTest {

    @Mock
    private EmployeeService employeeService;

    @Mock
    private Model model;

    @InjectMocks
    private EmployeeController employeeController;

    private Employee testEmployee;

    @BeforeEach
    public void setUp() {
        testEmployee = new Employee("John", "Doe", "john@example.com");
        testEmployee.setId(1L);
    }

    // ============================================
    // viewHomePage() Tests
    // ============================================

    @Test
    public void testViewHomePage() {
        List<Employee> employees = Arrays.asList(testEmployee);
        Page<Employee> page = new PageImpl<>(employees);
        
        when(employeeService.findPaginated(anyInt(), anyInt(), anyString(), anyString()))
            .thenReturn(page);

        String viewName = employeeController.viewHomePage(model);

        assertThat(viewName).isEqualTo("index");
        verify(employeeService).findPaginated(1, 5, "firstName", "asc");
    }

    @Test
    public void testViewHomePage_VerifyDefaultParameters() {
        Page<Employee> page = new PageImpl<>(Collections.emptyList());
        when(employeeService.findPaginated(1, 5, "firstName", "asc")).thenReturn(page);

        employeeController.viewHomePage(model);

        verify(employeeService).findPaginated(1, 5, "firstName", "asc");
        verify(employeeService, times(1)).findPaginated(anyInt(), anyInt(), anyString(), anyString());
    }

    @Test
    public void testViewHomePage_ReturnsIndexView() {
        Page<Employee> page = new PageImpl<>(Arrays.asList(testEmployee));
        when(employeeService.findPaginated(anyInt(), anyInt(), anyString(), anyString())).thenReturn(page);

        String result = employeeController.viewHomePage(model);

        assertThat(result).isNotNull();
        assertThat(result).isEqualTo("index");
    }

    // ============================================
    // showNewEmployeeForm() Tests
    // ============================================

    @Test
    public void testShowNewEmployeeForm() {
        String viewName = employeeController.showNewEmployeeForm(model);

        assertThat(viewName).isEqualTo("new_employee");
        verify(model).addAttribute(eq("employee"), any(Employee.class));
    }

    @Test
    public void testShowNewEmployeeForm_VerifyModelAttribute() {
        employeeController.showNewEmployeeForm(model);

        verify(model, times(1)).addAttribute(eq("employee"), any(Employee.class));
    }

    @Test
    public void testShowNewEmployeeForm_ReturnsCorrectView() {
        String result = employeeController.showNewEmployeeForm(model);

        assertThat(result).isNotNull();
        assertThat(result).isEqualTo("new_employee");
    }

    // ============================================
    // saveEmployee() Tests
    // ============================================

    @Test
    public void testSaveEmployee() {
        doNothing().when(employeeService).saveEmployee(any(Employee.class));

        String viewName = employeeController.saveEmployee(testEmployee);

        assertThat(viewName).isEqualTo("redirect:/");
        verify(employeeService).saveEmployee(testEmployee);
    }

    @Test
    public void testSaveEmployee_VerifyServiceCall() {
        Employee newEmployee = new Employee("Jane", "Smith", "jane@test.com");
        doNothing().when(employeeService).saveEmployee(newEmployee);

        employeeController.saveEmployee(newEmployee);

        verify(employeeService, times(1)).saveEmployee(newEmployee);
        verify(employeeService).saveEmployee(argThat(emp -> 
            emp.getFirstName().equals("Jane")
        ));
    }

    @Test
    public void testSaveEmployee_RedirectsToHome() {
        doNothing().when(employeeService).saveEmployee(any(Employee.class));

        String result = employeeController.saveEmployee(testEmployee);

        assertThat(result).startsWith("redirect:");
        assertThat(result).isEqualTo("redirect:/");
    }

    @Test
    public void testSaveEmployee_WithDifferentEmployees() {
        Employee emp1 = new Employee("Alice", "Wonder", "alice@test.com");
        Employee emp2 = new Employee("Bob", "Builder", "bob@test.com");
        
        doNothing().when(employeeService).saveEmployee(any(Employee.class));

        employeeController.saveEmployee(emp1);
        employeeController.saveEmployee(emp2);

        verify(employeeService, times(2)).saveEmployee(any(Employee.class));
    }

    // ============================================
    // showFormForUpdate() Tests
    // ============================================

    @Test
    public void testShowFormForUpdate() {
        when(employeeService.getEmployeeById(1L)).thenReturn(testEmployee);

        String viewName = employeeController.showFormForUpdate(1L, model);

        assertThat(viewName).isEqualTo("update_employee");
        verify(employeeService).getEmployeeById(1L);
        verify(model).addAttribute("employee", testEmployee);
    }

    @Test
    public void testShowFormForUpdate_VerifyServiceCall() {
        when(employeeService.getEmployeeById(5L)).thenReturn(testEmployee);

        employeeController.showFormForUpdate(5L, model);

        verify(employeeService, times(1)).getEmployeeById(5L);
        verify(employeeService, never()).getEmployeeById(1L);
    }

    @Test
    public void testShowFormForUpdate_VerifyModelAttribute() {
        Employee employee = new Employee("Update", "Test", "update@test.com");
        employee.setId(10L);
        when(employeeService.getEmployeeById(10L)).thenReturn(employee);

        employeeController.showFormForUpdate(10L, model);

        verify(model).addAttribute("employee", employee);
        verify(model, times(1)).addAttribute(anyString(), any());
    }

    @Test
    public void testShowFormForUpdate_ReturnsCorrectView() {
        when(employeeService.getEmployeeById(anyLong())).thenReturn(testEmployee);

        String result = employeeController.showFormForUpdate(1L, model);

        assertThat(result).isNotNull();
        assertThat(result).isEqualTo("update_employee");
    }

    @Test
    public void testShowFormForUpdate_DifferentEmployeeIds() {
        Employee emp1 = new Employee("Emp1", "Test", "emp1@test.com");
        emp1.setId(1L);
        Employee emp2 = new Employee("Emp2", "Test", "emp2@test.com");
        emp2.setId(2L);

        when(employeeService.getEmployeeById(1L)).thenReturn(emp1);
        when(employeeService.getEmployeeById(2L)).thenReturn(emp2);

        employeeController.showFormForUpdate(1L, model);
        employeeController.showFormForUpdate(2L, model);

        verify(employeeService).getEmployeeById(1L);
        verify(employeeService).getEmployeeById(2L);
    }

    // ============================================
    // deleteEmployee() Tests
    // ============================================

    @Test
    public void testDeleteEmployee() {
        doNothing().when(employeeService).deleteEmployeeById(1L);

        String viewName = employeeController.deleteEmployee(1L);

        assertThat(viewName).isEqualTo("redirect:/");
        verify(employeeService).deleteEmployeeById(1L);
    }

    @Test
    public void testDeleteEmployee_VerifyServiceCall() {
        doNothing().when(employeeService).deleteEmployeeById(99L);

        employeeController.deleteEmployee(99L);

        verify(employeeService, times(1)).deleteEmployeeById(99L);
        verify(employeeService, never()).deleteEmployeeById(1L);
    }

    @Test
    public void testDeleteEmployee_RedirectsToHome() {
        doNothing().when(employeeService).deleteEmployeeById(anyLong());

        String result = employeeController.deleteEmployee(5L);

        assertThat(result).startsWith("redirect:");
        assertThat(result).isEqualTo("redirect:/");
    }

    @Test
    public void testDeleteEmployee_MultipleDeletes() {
        doNothing().when(employeeService).deleteEmployeeById(anyLong());

        employeeController.deleteEmployee(1L);
        employeeController.deleteEmployee(2L);
        employeeController.deleteEmployee(3L);

        verify(employeeService).deleteEmployeeById(1L);
        verify(employeeService).deleteEmployeeById(2L);
        verify(employeeService).deleteEmployeeById(3L);
        verify(employeeService, times(3)).deleteEmployeeById(anyLong());
    }

    // ============================================
    // findPaginated() Tests
    // ============================================

    @Test
    public void testFindPaginated() {
        List<Employee> employees = Arrays.asList(testEmployee);
        Page<Employee> page = new PageImpl<>(employees);
        
        when(employeeService.findPaginated(1, 5, "firstName", "asc"))
            .thenReturn(page);

        String viewName = employeeController.findPaginated(1, "firstName", "asc", model);

        assertThat(viewName).isEqualTo("index");
        verify(employeeService).findPaginated(1, 5, "firstName", "asc");
        verify(model).addAttribute(eq("listEmployees"), anyList());
        verify(model).addAttribute("currentPage", 1);
        verify(model).addAttribute("totalPages", 1);
    }

    @Test
    public void testFindPaginatedWithDescendingSort() {
        List<Employee> employees = Arrays.asList(testEmployee);
        Page<Employee> page = new PageImpl<>(employees);
        
        when(employeeService.findPaginated(2, 5, "lastName", "desc"))
            .thenReturn(page);

        String viewName = employeeController.findPaginated(2, "lastName", "desc", model);

        assertThat(viewName).isEqualTo("index");
        verify(employeeService).findPaginated(2, 5, "lastName", "desc");
        verify(model).addAttribute("reverseSortDir", "asc");
    }

    @Test
    public void testFindPaginated_VerifyPageSize() {
        Page<Employee> page = new PageImpl<>(Collections.emptyList());
        when(employeeService.findPaginated(anyInt(), anyInt(), anyString(), anyString())).thenReturn(page);

        employeeController.findPaginated(1, "email", "asc", model);

        verify(employeeService).findPaginated(1, 5, "email", "asc");
    }

    @Test
    public void testFindPaginated_VerifyAllModelAttributes() {
        List<Employee> employees = Arrays.asList(testEmployee);
        Page<Employee> page = new PageImpl<>(employees);
        when(employeeService.findPaginated(1, 5, "firstName", "asc")).thenReturn(page);

        employeeController.findPaginated(1, "firstName", "asc", model);

        verify(model).addAttribute("currentPage", 1);
        verify(model).addAttribute("totalPages", 1);
        verify(model).addAttribute(eq("totalItems"), anyLong());
        verify(model).addAttribute("sortField", "firstName");
        verify(model).addAttribute("sortDir", "asc");
        verify(model).addAttribute("reverseSortDir", "desc");
        verify(model).addAttribute(eq("listEmployees"), anyList());
    }

    @Test
    public void testFindPaginated_AscendingSortReversesToDesc() {
        Page<Employee> page = new PageImpl<>(Collections.emptyList());
        when(employeeService.findPaginated(anyInt(), anyInt(), anyString(), anyString())).thenReturn(page);

        employeeController.findPaginated(1, "firstName", "asc", model);

        verify(model).addAttribute("reverseSortDir", "desc");
    }

    @Test
    public void testFindPaginated_DescendingSortReversesToAsc() {
        Page<Employee> page = new PageImpl<>(Collections.emptyList());
        when(employeeService.findPaginated(anyInt(), anyInt(), anyString(), anyString())).thenReturn(page);

        employeeController.findPaginated(1, "firstName", "desc", model);

        verify(model).addAttribute("reverseSortDir", "asc");
    }

    @Test
    public void testFindPaginated_DifferentPages() {
        Page<Employee> page = new PageImpl<>(Collections.emptyList());
        when(employeeService.findPaginated(anyInt(), anyInt(), anyString(), anyString())).thenReturn(page);

        employeeController.findPaginated(3, "email", "asc", model);

        verify(employeeService).findPaginated(3, 5, "email", "asc");
        verify(model).addAttribute("currentPage", 3);
    }

    @Test
    public void testFindPaginated_ReturnsIndexView() {
        Page<Employee> page = new PageImpl<>(Arrays.asList(testEmployee));
        when(employeeService.findPaginated(anyInt(), anyInt(), anyString(), anyString())).thenReturn(page);

        String result = employeeController.findPaginated(1, "firstName", "asc", model);

        assertThat(result).isNotNull();
        assertThat(result).isEqualTo("index");
    }

    @Test
    public void testFindPaginated_EmptyPage() {
        Page<Employee> emptyPage = new PageImpl<>(Collections.emptyList());
        when(employeeService.findPaginated(anyInt(), anyInt(), anyString(), anyString())).thenReturn(emptyPage);

        String viewName = employeeController.findPaginated(1, "firstName", "asc", model);

        assertThat(viewName).isEqualTo("index");
        verify(model).addAttribute(eq("listEmployees"), argThat(list -> 
            ((List<?>) list).isEmpty()
        ));
    }

    @Test
    public void testFindPaginated_VerifyListEmployeesContent() {
        List<Employee> employees = Arrays.asList(testEmployee);
        Page<Employee> page = new PageImpl<>(employees);
        when(employeeService.findPaginated(anyInt(), anyInt(), anyString(), anyString())).thenReturn(page);

        employeeController.findPaginated(1, "firstName", "asc", model);

        verify(model).addAttribute(eq("listEmployees"), argThat(list -> 
            list != null && ((List<?>) list).size() == 1
        ));
    }
}