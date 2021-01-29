/*
 * Author : Christopher Henard (christopher.henard@uni.lu)
 * Date : 21/05/2012
 * Copyright 2012 University of Luxembourg – Interdisciplinary Centre for Security Reliability and Trust (SnT)
 * All rights reserved
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.

 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.

 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package spl.fm;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

/**
 * This class represents a pair of features. Features are represented by a 
 * couple of integers, positive if the feature is selected, negative otherwise.
 * The integer value cannot be 0.
 *
 * If we consider the pair (1, 2), then (2, 1) denotes the same pair of features.
 * 
 * @author Christopher Henard
 */
public class TSet implements Serializable {

    private Set<Integer> vals;
    static final long serialVersionUID = -6618469844567325812L;

    public TSet(int[] vals) {
        this.vals = new HashSet<Integer>();
        for (Integer i : vals) {
            this.vals.add(i);
        }

    }

    public int getSize() {
        return vals.size();
    }

    public TSet() {
        this.vals = new HashSet<Integer>();
    }

    public void add(Integer i) {
        this.vals.add(i);
    }

    public Set<Integer> getVals() {
        return vals;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final TSet other = (TSet) obj;

        return vals.equals(other.vals);
    }

    @Override
    public int hashCode() {
        return vals.hashCode();
    }

    @Override
    public String toString() {
        return vals.toString();
    }
}
