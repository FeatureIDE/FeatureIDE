///*@ model import IntList; @*/

public class Main {

    public static void main(String[] args) {
        list = new IntList();
        list.push(2);
        list.snoc(4);
        list.push(5);
        list.snoc(1);
        
        list.printContents();
    }

}
