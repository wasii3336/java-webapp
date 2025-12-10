package crud.springboot;

import org.junit.jupiter.api.Test;
import org.springframework.boot.test.context.SpringBootTest;
import org.springframework.test.context.ActiveProfiles;

@SpringBootTest
@ActiveProfiles("test") // Use application-test.properties
class SpringbootThymeleafCrudWebAppApplicationTests {

    @Test
    void contextLoads() {
        // Test will pass if Spring context loads successfully
    }
}
