package announcement;

public class Hello implements interfaces.Announce{
@Override
public void announce() {
	System.err.print(" "+GREETINGS+" ");	
}
}
