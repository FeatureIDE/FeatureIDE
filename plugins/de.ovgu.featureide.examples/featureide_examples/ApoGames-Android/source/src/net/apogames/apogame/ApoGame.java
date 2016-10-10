package net.apogames.apogame;

import android.content.Context;
import android.content.SharedPreferences;
import android.net.ConnectivityManager;
import android.net.NetworkInfo;

import net.apogames.apogame.game.ApoGamePanel;

import net.gliblybits.bitsengine.core.BitsApp;
import net.gliblybits.bitsengine.core.BitsGame;
import net.gliblybits.bitsengine.utils.BitsLog;

public class ApoGame extends BitsApp {

	public static SharedPreferences settings;
	
	public static NetworkInfo ni;
	
	@Override
	protected void onCreate( ) 
	{
		BitsLog.setLogType(BitsLog.TYPE_NONE);
		
		BitsGame.sWantFullscreen = true;
		BitsGame.sOrientationMode = BitsGame.ORIENTATION_PORTRAIT;
		BitsGame.sGameWidth = 480;
		BitsGame.sGameHeight = 640;
		BitsGame.sWantTitleBar = false;
		BitsGame.sMaxRenderCommands = 1000;
		BitsGame.sMaxImageCount = 10;
		BitsGame.sMaxCirclePoints = 180;
		BitsGame.sMaxFPS = 60;
		BitsGame.sMaxTouchPointer = 3;
		BitsGame.sSleepMode = BitsGame.SLEEP_MODE_OFF;
		BitsGame.sWantMusic = false;
		BitsGame.sWantSound = false;
		BitsGame.sMaxFontCount = 3;
		
		ConnectivityManager cm = (ConnectivityManager)this.getSystemService(Context.CONNECTIVITY_SERVICE);
		ApoGame.ni = cm.getActiveNetworkInfo();
		
		ApoGame.settings = this.getSharedPreferences(ApoGameConstants.PREFS_NAME, 0);
		
		BitsGame.getIt().addScreen(new ApoGamePanel(1));
	}
	
	public static boolean isOnline() {
		if (ApoGame.ni == null) {
			return false;
		}
		return ApoGame.ni.isConnected();
	}

	@Override
	protected void onFinish( ) {
	}
}