package crud.springboot.model;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class EmployeeModelTest {

    @Test
    public void testEmployeeConstructorAndGetters() {
        Employee e = new Employee("John","Doe","john@example.com");
        assertEquals("John", e.getFirstName());
        assertEquals("Doe", e.getLastName());
        assertEquals("john@example.com", e.getEmail());
    }

    @Test
    public void testEmployeeSetters() {
        Employee e = new Employee();
        e.setId(1);
        e.setFirstName("Mike");
        e.setLastName("Smith");
        e.setEmail("mike@example.com");

        assertEquals(1,e.getId());
        assertEquals("Mike", e.getFirstName());
        assertEquals("Smith", e.getLastName());
        assertEquals("mike@example.com", e.getEmail());
    }

    @Test
    public void testNoArgsConstructor() {
        Employee e = new Employee();
        assertNotNull(e);
    }
}
