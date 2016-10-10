class Actions{
    private String findword; //for searching & finding the word
    //this is a method for searching the input text from the text area

    public void finD(){
        try{
            //this is an input dialog which return a string (findword)
            findword = JOptionPane.showInputDialog("Type the word to find");
            //if the JTextField in the input dialog is empty (null), then return a message dialog
            while(n.getTextArea().getText().indexOf(findword) == -1){
                /**
                 *this is a message dialog which is warning the user,
                 *because he didn't or forgot to enter the word
                 */
                JOptionPane.showMessageDialog(null,"Word not found!","No match",JOptionPane.WARNING_MESSAGE);
                findword = JOptionPane.showInputDialog("Type the word to find");
            }
            //for selecting the word which the user search for it
            n.getTextArea().select(n.getTextArea().getText().indexOf(findword),
            n.getTextArea().getText().indexOf(findword) + findword.length());
        }
        catch(Exception ex){
            JOptionPane.showMessageDialog(null,"Search canceled","Abourted",JOptionPane.WARNING_MESSAGE);
        }
    }
    public void findNexT(){
        n.getTextArea().select(n.getTextArea().getText().indexOf(findword,(int)n.getTextArea().getText().indexOf(findword)+1),
        n.getTextArea().getText().indexOf(findword,(int)n.getTextArea().getText().indexOf(findword)+1));
    }

}
