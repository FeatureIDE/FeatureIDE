
public class Profile {

    private String name;
    private int matches, s, u, n;

    public Profile(String name) {
        this.name = name;
        s = 0;
        u = 0;
        n = 0;
    }

    public int getMatches() {
        return matches;
    }

    public void setMatches(int matches) {
        this.matches = matches;
    }

    public int getN() {
        return n;
    }

    public void setN(int n) {
        this.n = n;
    }

    public String getName() {
        return name;
    }

    public int getS() {
        return s;
    }

    public void setS(int s) {
        this.s = s;
    }

    public int getU() {
        return u;
    }

    public void setU(int u) {
        this.u = u;
    }

}
