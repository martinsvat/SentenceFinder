package ida.utils;

/**
 * Created by kuzelkao_cardiff on 17/03/17.
 */
public class MutableBoolean {

    private boolean value;

    public MutableBoolean(boolean value){
        this.value = value;
    }

    public void set(boolean value){
        this.value = value;
    }

    public boolean value(){
        return this.value;
    }

    public String toString(){
        return Boolean.toString(this.value);
    }

    public int hashCode(){
        return Boolean.hashCode(this.value);
    }

    public boolean equals(Object o){
        if (o instanceof MutableBoolean){
            return ((MutableBoolean)o).value == this.value;
        }
        return false;
    }

}
