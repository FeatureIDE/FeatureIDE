public class IntList {
    
    /*@
    @ ensures (data[0] == newElem) 
    @    && (\forall int k; 0 <= k && k < \old(data).length; \old(data)[k] == data[k+1]);
    @ assignable data;
    @*/
    public void snoc(int newElem) {
        int[] tmp = new int[data.length+1];
        tmp[0] = newElem;
        for(int i = 0; i < data.length; i++) {
            tmp[i+1] = data[i];
        }
        //@ assert tmp[0] == newElem;
        data = tmp;
    }
    
}
