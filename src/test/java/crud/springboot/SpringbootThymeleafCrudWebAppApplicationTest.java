package crud.springboot;

import org.junit.jupiter.api.Test;
import org.springframework.boot.SpringApplication;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

class SpringbootThymeleafCrudWebAppApplicationTest {

    @Test
    void mainMethodRuns() {
        assertDoesNotThrow(() ->
            SpringbootThymeleafCrudWebAppApplication.main(new String[] {})
        );
    }
}
