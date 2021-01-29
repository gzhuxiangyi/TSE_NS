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

package spl.techniques;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import spl.fm.Product;

/**
 *
 * @author Christopher Henard
 */
public class RandomTechnique implements PrioritizationTechnique {

    private static Random randGen = new Random();

    @Override
    public List<Product> prioritize(List<Product> products) {
        List<Product> productsCopy = new ArrayList<Product>(products);
        List<Product> randomizedProducts = new ArrayList<Product>(productsCopy.size());
        while (!productsCopy.isEmpty()) {
            int rand = randGen.nextInt(productsCopy.size());
            randomizedProducts.add(productsCopy.get(rand));
            productsCopy.remove(rand);
        }
        return randomizedProducts;
    }
}
