package crud.springboot.stubs;

import java.util.List;

public class Page<T> {
    /*@ spec_public @*/ private List<T> content;
    
    //@ public invariant content != null;
    
    /*@ requires content != null;
      @ ensures this.content == content;
      @*/
    public Page(List<T> content) {
        this.content = content;
    }
    
    /*@ public normal_behavior
      @   ensures \result != null;
      @ pure
      @*/
    public List<T> getContent() {
        return content;
    }
    
    /*@ public normal_behavior
      @   ensures \result >= 0;
      @   ensures \result == content.size();
      @ pure
      @*/
    public int getSize() {
        return content.size();
    }
    
    /*@ public normal_behavior
      @   ensures \result == (content.size() == 0);
      @ pure
      @*/
    public boolean isEmpty() {
        return content.isEmpty();
    }
}