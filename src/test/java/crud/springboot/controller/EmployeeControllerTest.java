package crud.springboot.controller;

import crud.springboot.model.Employee;
import crud.springboot.service.EmployeeService;

import org.junit.jupiter.api.Test;

import org.mockito.Mockito;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.web.servlet.WebMvcTest;

import org.springframework.boot.test.mock.mockito.MockBean;
import org.springframework.data.domain.*;
import org.springframework.test.web.servlet.MockMvc;

import java.util.List;

import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.when;
import static org.springframework.test.web.servlet.request.MockMvcRequestBuilders.*;
import static org.springframework.test.web.servlet.result.MockMvcResultMatchers.*;

@WebMvcTest(EmployeeController.class)
class EmployeeControllerTest {

    @Autowired
    private MockMvc mockMvc;

    @MockBean
    private EmployeeService employeeService;

    @Test
    void testViewHomePage() throws Exception {
        Page<Employee> page = new PageImpl<>(List.of(new Employee("A", "B", "a@b.com")));
        when(employeeService.findPaginated(Mockito.anyInt(), Mockito.anyInt(), any(), any()))
                .thenReturn(page);

        mockMvc.perform(get("/"))
                .andExpect(status().isOk())
                .andExpect(view().name("index"));
    }

    @Test
    void testShowNewEmployeeForm() throws Exception {
        mockMvc.perform(get("/showNewEmployeeForm"))
                .andExpect(status().isOk())
                .andExpect(view().name("new_employee"));
    }

    @Test
    void testSaveEmployee() throws Exception {
        mockMvc.perform(post("/saveEmployee")
                .param("firstName", "John")
                .param("lastName", "Doe")
                .param("email", "john@example.com"))
                .andExpect(status().is3xxRedirection())
                .andExpect(redirectedUrl("/"));
    }

    @Test
    void testDeleteEmployee() throws Exception {
        mockMvc.perform(get("/deleteEmployee/1"))
                .andExpect(status().is3xxRedirection())
                .andExpect(redirectedUrl("/"));
    }
    @Test
void testShowFormForUpdate() throws Exception {
    Employee e = new Employee("John", "Doe", "john@test.com");
    e.setId(1);

    when(employeeService.getEmployeeById(1L)).thenReturn(e);

    mockMvc.perform(get("/showFormForUpdate/1"))
            .andExpect(status().isOk())
            .andExpect(model().attributeExists("employee"))
            .andExpect(view().name("update_employee"));
    }
    @Test
void testFindPaginated() throws Exception {
    Page<Employee> page = new PageImpl<>(List.of(new Employee("A", "B", "a@b.com")));

    when(employeeService.findPaginated(1, 5, "firstName", "asc"))
            .thenReturn(page);

    mockMvc.perform(get("/page/1")
            .param("sortField", "firstName")
            .param("sortDir", "asc"))
            .andExpect(status().isOk())
            .andExpect(view().name("index"))
            .andExpect(model().attributeExists("listEmployees"))
            .andExpect(model().attributeExists("totalPages"))
            .andExpect(model().attributeExists("totalItems"));
}
        
}
