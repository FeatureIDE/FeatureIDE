
public class IntList {
    
  /*@ 
    @ requires data.length > 0; 
    @ assignable \nothing;
    @ ensures \result == data[data.length-1];
    @*/
  public int top() {
      return data[data.length-1];
  }
  
  /*@ 
    @ requires data.length > 0; 
    @ assignable data;
    @ ensures \result == \old(data)[\old(data).length-1] 
    @ && data.length == \old(data).length - 1
    @ && (\forall int k; 0 <= k && k < \old(data).length-1;
    @    (\exists int z; 0 <= z && z < data.length; data[z] == \old(data)[k]) );
    @*/
  public int pop() {
      int result = data[data.length-1];
      int[] tmp = new int[data.length-1];
      for(int i = 0; i < tmp.length; i++) {
          tmp[i] = data[i];
      }
      data = tmp;
      //@ assert result == \old(data)[\old(data).length-1];
      return result;
  }
  
  /*@ ensures \result <==> (data.length == 0);
    @*/
  public boolean isEmpty() {
	  return data.length == 0;
  }
    
}
