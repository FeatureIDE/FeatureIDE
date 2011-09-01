
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import javax.swing.JOptionPane;
import javax.swing.JTextField;

public class LoadSave {

    String[] datenRein = new String[5];
    String[] datenRaus = new String[5];

    public LoadSave() {
    }

    public void createNewPlayer(){
        JTextField name = new JTextField();
                Object[] message = {"Name", name};

        JOptionPane pane = new JOptionPane(message,
                                                JOptionPane.PLAIN_MESSAGE,
                                                JOptionPane.OK_CANCEL_OPTION);
        pane.createDialog(null, "Neues Profil anlegen").setVisible(true);
                
        System.out.println("Eingabe Name: " + name.getText());
        datenRaus[0] = name.getText();
        datenRaus[1] = "0";
        datenRaus[2] = "0";
        datenRaus[3] = "0";
        datenRaus[4] = "0";

        File pfad = new File("");
        System.out.println(pfad.getAbsolutePath());
        this.save(pfad.getAbsolutePath().concat("/data/" + name.getText() + ".dat"), datenRaus);
    }

    public void save(String file, Object[] datenRaus) {
        try {
            BufferedWriter writer = new BufferedWriter(new FileWriter(file));
                        for (int i = 0; i < datenRaus.length; i++)
                                   writer.write(datenRaus[i] + ";");
            writer.close();
        }
        catch (IOException e) {
            e.printStackTrace();
        }
    }

    public String[] load(File file){
        BufferedReader reader;
        try {
            reader = new BufferedReader(new FileReader(file));
            String zeile = reader.readLine();
            while (zeile != null) {
                datenRein = zeile.split(";");
            }
        }
        catch (IOException e) {
            e.printStackTrace();
        }
        return datenRein;
    }   

}
