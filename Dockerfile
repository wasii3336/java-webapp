# Stage 1: Build JAR (skip tests during Docker build)
FROM maven:3.9.3-eclipse-temurin-17 AS build
WORKDIR /app
COPY pom.xml .
COPY src ./src

# Build without running tests (tests run in CI/CD separately)
RUN mvn clean package -DskipTests

# Stage 2: Run JAR
FROM eclipse-temurin:17-jdk
WORKDIR /app

# Copy built JAR
COPY --from=build /app/target/*.jar app.jar

EXPOSE 8080

ENTRYPOINT ["java", "-jar", "app.jar"]
