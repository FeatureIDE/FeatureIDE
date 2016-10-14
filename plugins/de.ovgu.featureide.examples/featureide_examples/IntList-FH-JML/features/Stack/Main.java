///*@ model import IntList; @*/

public class Main {

    public static void main(String[] args) {
        original(args);
        
        System.out.print("Stack elements: ");
        while (!list.isEmpty()) {
        	System.out.print(list.pop());
        }
        System.out.println();
        
        list.printContents();
    }

}
