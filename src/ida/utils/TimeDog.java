package ida.utils;

/**
 * Created by martin.svatos on 05.05.2017.
 * <p>
 * When doNotUseTime is set to True, the watchdog is not used; otherwise the limit is counted.
 */
public class TimeDog {

    private final long last;
    private final long limit;
    private final boolean doNotUseTime;
    private final long start;

    public TimeDog(long nanoLimit, boolean doNotUseTime) {
        this.limit = nanoLimit;
        this.doNotUseTime = doNotUseTime;
        this.last = System.nanoTime() + nanoLimit;
        this.start = System.nanoTime();
    }

    public TimeDog(long nanoLimit) {
        this(nanoLimit, false);
    }


    public boolean isOut() {
        return System.nanoTime() > this.last && !doNotUseTime;
    }

    public boolean enough() { // tady redundance v tom dotazu na doNotUseTime
        return doNotUseTime || !isOut();
    }

    public TimeDog fromNow() {
        return new TimeDog(limit, this.doNotUseTime);
    }

    public long getLast() {
        return last;
    }

    public long getLimit() {
        return limit;
    }

    public boolean doNotUseTime() {
        return doNotUseTime;
    }

    public String left() {
        if (doNotUseTime) {
            return "forever";
        }
        return ((last - System.nanoTime()) * 1.0 / 1000000000) + "";
    }

    public String getSecondsFromStart() {
        return (getNanoFromStart() / 1000000000) + " seconds";
    }

    public Long getNanoFromStart() {
        return System.nanoTime() - this.start;
    }
}
