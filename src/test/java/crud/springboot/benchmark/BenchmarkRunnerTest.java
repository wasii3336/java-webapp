package crud.springboot.benchmark;

import org.junit.jupiter.api.Test;

/**
 * JUnit wrapper to run JMH benchmarks through Maven test phase.
 * This makes it easy to run benchmarks without manually handling classpaths.
 */
public class BenchmarkRunnerTest {

    @Test
    void runJMHBenchmarks() throws Exception {
        BenchmarkRunner.main(new String[]{});
    }
}
