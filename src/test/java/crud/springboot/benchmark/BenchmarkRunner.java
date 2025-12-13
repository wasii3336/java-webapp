package crud.springboot.benchmark;

import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

/**
 * Main class to run JMH benchmarks
 * 
 * Usage:
 * 1. Compile: mvn clean test-compile
 * 2. Run: java -cp target/test-classes:target/classes:~/.m2/repository/... crud.springboot.benchmark.BenchmarkRunner
 * 
 * Or simply run as a Java application from your IDE
 */
public class BenchmarkRunner {
    
    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(EmployeeServiceBenchmark.class.getSimpleName())
                .forks(0) // Disable forking - run in same JVM
                .warmupIterations(2)
                .measurementIterations(3)
                .shouldFailOnError(true)
                .build();

        new Runner(opt).run();
    }
}