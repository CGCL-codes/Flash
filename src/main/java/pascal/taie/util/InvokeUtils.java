package pascal.taie.util;

import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;

public class InvokeUtils {

    public static final int BASE = -1;

    /**
     * String representation of base variable.
     */
    private static final String BASE_STR = "base";

    /**
     * Special number representing the variable that receivers
     * the result of the invocation.
     */
    public static final int RESULT = -2;

    /**
     * String representation of result variable.
     */
    private static final String RESULT_STR = "result";

    private InvokeUtils() {
    }

    /**
     * Coverts string to index.
     */
    public static int toInt(String s) {
        return switch (s.toLowerCase()) {
            case BASE_STR -> BASE;
            case RESULT_STR -> RESULT;
            case "polluted" -> -2;
            default -> Integer.parseInt(s);
        };
    }

    /**
     * Converts index to string.
     */
    public static String toString(int index) {
        return switch (index) {
            case BASE -> BASE_STR;
            case RESULT -> RESULT_STR;
            default -> Integer.toString(index);
        };
    }

    /**
     * Retrieves variable from a call site and index.
     */
    public static Var getVar(Invoke callSite, int index) {
        InvokeExp invokeExp = callSite.getInvokeExp();
        return switch (index) {
            case BASE -> ((InvokeInstanceExp) invokeExp).getBase();
            case RESULT -> callSite.getResult();
            default -> invokeExp.getArg(index);
        };
    }

}
