/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.util;

import pascal.taie.analysis.dataflow.analysis.methodsummary.Utils.ContrUtil;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Static utility methods for {@link String}.
 */
public final class Strings {

    private Strings() {
    }

    /**
     * Capitalizes a {@link String}, changing the first letter to upper case
     * as per {@link Character#toUpperCase(char)}. No other letters are changed.
     *
     * @param str the {@link String} to capitalize
     * @return the capitalized {@link String}
     */
    public static String capitalize(String str) {
        if (str == null || str.isEmpty()) {
            return str;
        }
        char oldFirst = str.charAt(0);
        char newFirst = Character.toUpperCase(oldFirst);
        if (oldFirst == newFirst) {
            return str;
        }
        char[] chars = str.toCharArray();
        chars[0] = newFirst;
        return new String(chars);
    }

    public static boolean isLegalContrValue(String value) {
        return value.matches("[a-zA-Z0-9_+\\-.: ]*");
    }

    public static int extractParamIndex(String s) {
        String regex = "param-(\\d+)";
        Pattern pattern = Pattern.compile(regex);
        Matcher matcher = pattern.matcher(s);

        if (matcher.find()) {
            int value = Integer.parseInt(matcher.group(1));
            return value;
        } else {
            return ContrUtil.iNOT_POLLUTED;
        }
    }

    public static String extractFieldName(String s) {
        if (s.startsWith(ContrUtil.sParam)) {
            return s.split("-")[2];
        }
        int _idx = s.indexOf("-");
        String last = s.substring(_idx + 1);
        if (last.contains("+")) {
            String former = last.split("\\+")[0];
            if (former.isEmpty()) return extractFieldName(last.split("\\+")[1]);
            return former.contains("-") ? former.split("-")[0] : former;
        }
        else if (last.contains("-")) return last.split("-")[0];
        else return last;
    }

    public static boolean anyMatch(String reg) {
        return reg.equals(".*");
    }
}
