package crud.springboot.benchmark;

import crud.springboot.model.Employee;
import crud.springboot.repository.EmployeeRepository;
import crud.springboot.service.impl.EmployeeServiceImpl;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.springframework.data.domain.Page;
import org.springframework.data.domain.PageImpl;
import org.springframework.data.domain.PageRequest;
import org.springframework.data.domain.Sort;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.TimeUnit;

import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

/**
 * JMH Benchmark for EmployeeService performance testing
 * 
 * Run with: mvn clean test-compile exec:exec@run-benchmarks
 * Or: java -jar target/benchmarks.jar
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Benchmark)
@Fork(value = 1, warmups = 1)
@Warmup(iterations = 3, time = 1)
@Measurement(iterations = 5, time = 1)
public class EmployeeServiceBenchmark {

    private EmployeeServiceImpl employeeService;
    private EmployeeRepository employeeRepository;
    private List<Employee> smallDataset;
    private List<Employee> mediumDataset;
    private List<Employee> largeDataset;

    @Setup(Level.Trial)
    public void setup() {
        employeeRepository = mock(EmployeeRepository.class);
        employeeService = new EmployeeServiceImpl();
        
        // Use reflection to inject the mocked repository
        try {
            java.lang.reflect.Field field = EmployeeServiceImpl.class.getDeclaredField("employeeRepository");
            field.setAccessible(true);
            field.set(employeeService, employeeRepository);
        } catch (Exception e) {
            throw new RuntimeException("Failed to inject repository", e);
        }

        // Prepare datasets
        smallDataset = createEmployeeList(10);
        mediumDataset = createEmployeeList(100);
        largeDataset = createEmployeeList(1000);

        // Mock repository responses
        when(employeeRepository.findAll()).thenReturn(mediumDataset);
        when(employeeRepository.findById(any(Long.class)))
            .thenReturn(Optional.of(mediumDataset.get(0)));
        when(employeeRepository.save(any(Employee.class)))
            .thenAnswer(invocation -> invocation.getArgument(0));
    }

    private List<Employee> createEmployeeList(int size) {
        List<Employee> employees = new ArrayList<>(size);
        for (int i = 0; i < size; i++) {
            Employee emp = new Employee(
                "FirstName" + i,
                "LastName" + i,
                "email" + i + "@test.com"
            );
            emp.setId((long) i);
            employees.add(emp);
        }
        return employees;
    }

    // ============================================
    // Benchmark: getAllEmployees()
    // ============================================

    @Benchmark
    public void benchmarkGetAllEmployees_Small(Blackhole blackhole) {
        when(employeeRepository.findAll()).thenReturn(smallDataset);
        List<Employee> result = employeeService.getAllEmployees();
        blackhole.consume(result);
    }

    @Benchmark
    public void benchmarkGetAllEmployees_Medium(Blackhole blackhole) {
        when(employeeRepository.findAll()).thenReturn(mediumDataset);
        List<Employee> result = employeeService.getAllEmployees();
        blackhole.consume(result);
    }

    @Benchmark
    public void benchmarkGetAllEmployees_Large(Blackhole blackhole) {
        when(employeeRepository.findAll()).thenReturn(largeDataset);
        List<Employee> result = employeeService.getAllEmployees();
        blackhole.consume(result);
    }

    // ============================================
    // Benchmark: saveEmployee()
    // ============================================

    @Benchmark
    public void benchmarkSaveEmployee(Blackhole blackhole) {
        Employee employee = new Employee("John", "Doe", "john@test.com");
        employeeService.saveEmployee(employee);
        blackhole.consume(employee);
    }

    @Benchmark
    public void benchmarkSaveEmployee_WithId(Blackhole blackhole) {
        Employee employee = new Employee("Jane", "Smith", "jane@test.com");
        employee.setId(999L);
        employeeService.saveEmployee(employee);
        blackhole.consume(employee);
    }

    // ============================================
    // Benchmark: getEmployeeById()
    // ============================================

    @Benchmark
    public void benchmarkGetEmployeeById(Blackhole blackhole) {
        Employee result = employeeService.getEmployeeById(1L);
        blackhole.consume(result);
    }

    @Benchmark
    public void benchmarkGetEmployeeById_MultipleCalls(Blackhole blackhole) {
        for (int i = 0; i < 10; i++) {
            Employee result = employeeService.getEmployeeById((long) i);
            blackhole.consume(result);
        }
    }

    // ============================================
    // Benchmark: deleteEmployeeById()
    // ============================================

    @Benchmark
    public void benchmarkDeleteEmployeeById() {
        employeeService.deleteEmployeeById(1L);
    }

    @Benchmark
    public void benchmarkDeleteEmployeeById_Multiple() {
        for (int i = 0; i < 10; i++) {
            employeeService.deleteEmployeeById((long) i);
        }
    }

    // ============================================
    // Benchmark: findPaginated() - Most demanding
    // ============================================

    @Benchmark
    public void benchmarkFindPaginated_SmallPage(Blackhole blackhole) {
        Page<Employee> page = new PageImpl<>(smallDataset.subList(0, Math.min(5, smallDataset.size())));
        when(employeeRepository.findAll(any(PageRequest.class))).thenReturn(page);
        
        Page<Employee> result = employeeService.findPaginated(1, 5, "firstName", "asc");
        blackhole.consume(result);
    }

    @Benchmark
    public void benchmarkFindPaginated_MediumPage(Blackhole blackhole) {
        Page<Employee> page = new PageImpl<>(mediumDataset.subList(0, Math.min(10, mediumDataset.size())));
        when(employeeRepository.findAll(any(PageRequest.class))).thenReturn(page);
        
        Page<Employee> result = employeeService.findPaginated(1, 10, "firstName", "asc");
        blackhole.consume(result);
    }

    @Benchmark
    public void benchmarkFindPaginated_LargePage(Blackhole blackhole) {
        Page<Employee> page = new PageImpl<>(largeDataset.subList(0, Math.min(50, largeDataset.size())));
        when(employeeRepository.findAll(any(PageRequest.class))).thenReturn(page);
        
        Page<Employee> result = employeeService.findPaginated(1, 50, "firstName", "asc");
        blackhole.consume(result);
    }

    @Benchmark
    public void benchmarkFindPaginated_DifferentSortFields(Blackhole blackhole) {
        Page<Employee> page = new PageImpl<>(mediumDataset.subList(0, 10));
        when(employeeRepository.findAll(any(PageRequest.class))).thenReturn(page);
        
        // Test different sort fields
        Page<Employee> result1 = employeeService.findPaginated(1, 10, "firstName", "asc");
        Page<Employee> result2 = employeeService.findPaginated(1, 10, "lastName", "desc");
        Page<Employee> result3 = employeeService.findPaginated(1, 10, "email", "asc");
        
        blackhole.consume(result1);
        blackhole.consume(result2);
        blackhole.consume(result3);
    }

    @Benchmark
    public void benchmarkFindPaginated_MultiplePages(Blackhole blackhole) {
        Page<Employee> page = new PageImpl<>(mediumDataset.subList(0, 10));
        when(employeeRepository.findAll(any(PageRequest.class))).thenReturn(page);
        
        // Simulate browsing through multiple pages
        for (int i = 1; i <= 5; i++) {
            Page<Employee> result = employeeService.findPaginated(i, 10, "firstName", "asc");
            blackhole.consume(result);
        }
    }

    // ============================================
    // Throughput Benchmark
    // ============================================

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.SECONDS)
    public void benchmarkThroughput_GetAllEmployees(Blackhole blackhole) {
        when(employeeRepository.findAll()).thenReturn(mediumDataset);
        List<Employee> result = employeeService.getAllEmployees();
        blackhole.consume(result);
    }

    @Benchmark
    @BenchmarkMode(Mode.Throughput)
    @OutputTimeUnit(TimeUnit.SECONDS)
    public void benchmarkThroughput_FindPaginated(Blackhole blackhole) {
        Page<Employee> page = new PageImpl<>(mediumDataset.subList(0, 10));
        when(employeeRepository.findAll(any(PageRequest.class))).thenReturn(page);
        
        Page<Employee> result = employeeService.findPaginated(1, 10, "firstName", "asc");
        blackhole.consume(result);
    }
}