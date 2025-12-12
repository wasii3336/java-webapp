# Stage 1: Build JAR and run tests (JaCoCo report generated)
FROM maven:3.9.3-eclipse-temurin-17 AS build
WORKDIR /app
COPY pom.xml .
COPY src ./src

# Run tests with JaCoCo enabled
RUN mvn clean verify

# Stage 2: Run JAR
FROM eclipse-temurin:17-jdk
WORKDIR /app

# Copy built JAR
COPY --from=build /app/target/*.jar app.jar

# Copy JaCoCo HTML report to runtime container (optional)
COPY --from=build /app/target/site/jacoco /app/jacoco

EXPOSE 8080

ENTRYPOINT ["java", "-jar", "app.jar"]
