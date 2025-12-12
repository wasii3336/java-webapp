package crud.springboot.stubs;

public class Employee {
    /*@ spec_public @*/ private long id;
    /*@ spec_public @*/ private String firstName;
    /*@ spec_public @*/ private String lastName;
    /*@ spec_public @*/ private String email;
    
    //@ public invariant id >= 0;
    //@ public invariant firstName != null;
    //@ public invariant lastName != null;
    //@ public invariant email != null;
    
    public Employee() {
        this.id = 0;
        this.firstName = "";
        this.lastName = "";
        this.email = "";
    }
    
    /*@ requires firstName != null;
      @ requires lastName != null;
      @ requires email != null;
      @ ensures this.id == id;
      @ ensures this.firstName == firstName;
      @ ensures this.lastName == lastName;
      @ ensures this.email == email;
      @*/
    public Employee(long id, String firstName, String lastName, String email) {
        this.id = id;
        this.firstName = firstName;
        this.lastName = lastName;
        this.email = email;
    }
    
    /*@ public normal_behavior
      @   ensures \result >= 0;
      @ pure
      @*/
    public long getId() { 
        return id; 
    }
    
    /*@ public normal_behavior
      @   ensures \result != null;
      @ pure
      @*/
    public String getFirstName() { 
        return firstName; 
    }
    
    /*@ public normal_behavior
      @   ensures \result != null;
      @ pure
      @*/
    public String getLastName() { 
        return lastName; 
    }
    
    /*@ public normal_behavior
      @   ensures \result != null;
      @ pure
      @*/
    public String getEmail() { 
        return email; 
    }
    
    /*@ requires id >= 0;
      @ ensures this.id == id;
      @*/
    public void setId(long id) { 
        this.id = id; 
    }
    
    /*@ requires firstName != null;
      @ ensures this.firstName == firstName;
      @*/
    public void setFirstName(String firstName) { 
        this.firstName = firstName; 
    }
    
    /*@ requires lastName != null;
      @ ensures this.lastName == lastName;
      @*/
    public void setLastName(String lastName) { 
        this.lastName = lastName; 
    }
    
    /*@ requires email != null;
      @ ensures this.email == email;
      @*/
    public void setEmail(String email) { 
        this.email = email; 
    }
    
    /*@ also
      @ public normal_behavior
      @ pure
      @*/
    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        Employee employee = (Employee) obj;
        return id == employee.id;
    }
    
    /*@ also
      @ public normal_behavior
      @ pure
      @*/
    @Override
    public int hashCode() {
        return Long.hashCode(id);
    }
}