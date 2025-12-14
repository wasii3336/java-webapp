package crud.springboot.model;

import jakarta.persistence.*;

/**
 * Employee entity with JML formal specifications
 */
@Entity
@Table(name = "employees")
public class Employee {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private long id;

    @Column(name = "first_name")
    private String firstName;

    @Column(name = "last_name")
    private String lastName;

    @Column(name = "email")
    private String email;

    //@ public invariant firstName == null || firstName.length() > 0;
    //@ public invariant lastName == null || lastName.length() > 0;
    //@ public invariant email == null || email.contains("@");

    /**
     * Default constructor required by JPA
     */
    //@ ensures getId() == 0;
    public Employee() {
    }

    /**
     * Convenience constructor for creating employees
     * @param firstName Employee's first name
     * @param lastName Employee's last name
     * @param email Employee's email address
     */
    //@ requires firstName != null && firstName.length() > 0;
    //@ requires lastName != null && lastName.length() > 0;
    //@ requires email != null && email.contains("@");
    //@ ensures getFirstName().equals(firstName);
    //@ ensures getLastName().equals(lastName);
    //@ ensures getEmail().equals(email);
    public Employee(String firstName, String lastName, String email) {
        this.firstName = firstName;
        this.lastName = lastName;
        this.email = email;
    }

    /**
     * Get employee ID
     * @return The employee ID
     */
    //@ ensures \result >= 0;
    //@ pure
    public long getId() {
        return id;
    }

    /**
     * Set employee ID
     * @param id The employee ID to set
     */
    //@ requires id >= 0;
    //@ ensures getId() == id;
    public void setId(long id) {
        this.id = id;
    }

    /**
     * Get employee first name
     * @return The first name
     */
    //@ pure
    public String getFirstName() {
        return firstName;
    }

    /**
     * Set employee first name
     * @param firstName The first name to set
     */
    //@ requires firstName != null && firstName.length() > 0;
    //@ ensures getFirstName().equals(firstName);
    public void setFirstName(String firstName) {
        this.firstName = firstName;
    }

    /**
     * Get employee last name
     * @return The last name
     */
    //@ pure
    public String getLastName() {
        return lastName;
    }

    /**
     * Set employee last name
     * @param lastName The last name to set
     */
    //@ requires lastName != null && lastName.length() > 0;
    //@ ensures getLastName().equals(lastName);
    public void setLastName(String lastName) {
        this.lastName = lastName;
    }

    /**
     * Get employee email
     * @return The email address
     */
    //@ pure
    public String getEmail() {
        return email;
    }

    /**
     * Set employee email
     * @param email The email address to set
     */
    //@ requires email != null && email.contains("@");
    //@ ensures getEmail().equals(email);
    public void setEmail(String email) {
        this.email = email;
    }
}