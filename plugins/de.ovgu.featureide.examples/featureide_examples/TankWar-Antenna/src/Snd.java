
import sun.audio.*;
import java.io.*;

public class Snd {

    public static void music(String snd){

        AudioPlayer MGP = AudioPlayer.player;
        AudioStream BGM;
        AudioData MD;
        AudioDataStream stream = null;

        try{
            BGM = new AudioStream(new FileInputStream(snd));
            MD = BGM.getData();
            stream = new AudioDataStream(MD);

            }
        catch(IOException error){}

        MGP.start(stream);
    }
}
