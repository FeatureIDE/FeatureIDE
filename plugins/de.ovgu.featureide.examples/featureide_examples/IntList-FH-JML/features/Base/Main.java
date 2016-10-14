///*@ model import IntList; @*/

public class Main {
	
	private static IntList list;

    public static void main(String[] args) {
        list = new IntList();
        list.push(2);
        list.push(4);
        list.push(5);
        list.push(1);
        
        list.printContents();
    }

}
