/* Copyright 2009-2015 David Hadka
 *
 * This file is part of the MOEA Framework.
 *
 * The MOEA Framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or (at your
 * option) any later version.
 *
 * The MOEA Framework is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
 * License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the MOEA Framework.  If not, see <http://www.gnu.org/licenses/>.
 */
package jmetal.core;

import java.awt.Image;
import java.awt.Toolkit;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

import jmetal.qualityIndicator.Hypervolume;

import org.apache.commons.lang3.text.StrTokenizer;

/**
 * Global settings used by this framework.  The {@code PROPERTIES} object
 * contains the system properties and optionally the contents of a 
 * configuration file (properties in the configuration file take precedence).
 * By default, the {@code global.properties} file is loaded, but can be
 * specified using the {@code org.moeaframework.configuration} system
 * property.
 */
public class Settings {

	/**
	 * Level of significance or machine precision.
	 */
	public static final double EPS = 1e-10;
	
	/**
	 * The default buffer size.  Currently set to 4096 bytes.
	 */
	public static final int BUFFER_SIZE = 0x1000;
	
	/**
	 * Store the new line character to prevent repetitive calls to
	 * {@code System.getProperty("line.separator")}.
	 */
	public static final String NEW_LINE = System.getProperty("line.separator");

	
	/**
	 * The prefix for all property keys.
	 */
	public static final String KEY_PREFIX = "org.moeaframework.";
	
	/**
	 * The property key for the continuity correction flag.
	 */
	public static final String KEY_CONTINUITY_CORRECTION = KEY_PREFIX +
			"util.statistics.continuity_correction";
	
	/**
	 * The property key for the hypervolume delta when determining the
	 * reference point.
	 */
	public static final String KEY_HYPERVOLUME_DELTA = KEY_PREFIX +
			"core.indicator.hypervolume_delta";
	
	/**
	 * The property key for the hypervolume command.
	 */
	public static final String KEY_HYPERVOLUME = KEY_PREFIX +
			"core.indicator.hypervolume";
	
	/**
	 * The property key for the hypervolume inversion flag.
	 */
	public static final String KEY_HYPERVOLUME_INVERTED = KEY_PREFIX + 
			"core.indicator.hypervolume_inverted";
	
	/**
	 * The property key for the hypervolume flag.
	 */
	public static final String KEY_HYPERVOLUME_ENABLED = KEY_PREFIX +
			"core.indicator.hypervolume_enabled";
	
	/**
	 * The prefix for all problem property keys.
	 */
	public static final String KEY_PROBLEM_PREFIX = KEY_PREFIX + "problem.";
	
	/**
	 * The property key for the list of available problems.
	 */
	public static final String KEY_PROBLEM_LIST = KEY_PROBLEM_PREFIX +
			"problems";
	
	/**
	 * The prefix for all PISA property keys.
	 */
	public static final String KEY_PISA_PREFIX = KEY_PREFIX + "algorithm.pisa.";
	
	/**
	 * The property key for the list of available PISA algorithms.
	 */
	public static final String KEY_PISA_ALGORITHMS = KEY_PISA_PREFIX + 
			"algorithms";
	
	/**
	 * The property key for the poll rate.
	 */
	public static final String KEY_PISA_POLL = KEY_PISA_PREFIX + "poll";
	
	/**
	 * The property key for the file protection mode.
	 */
	public static final String KEY_FILE_PROTECTION_MODE = KEY_PREFIX + 
			"util.io.file_protection_mode";
	
	/**
	 * The property key for the file protection file name format.
	 */
	public static final String KEY_FILE_PROTECTION_FORMAT = KEY_PREFIX +
			"util.io.file_protection_format";
	
	/**
	 * The property key for the algorithms available in the diagnostic tool.
	 */
	public static final String KEY_DIAGNOSTIC_TOOL_ALGORITHMS = KEY_PREFIX +
			"analysis.diagnostics.algorithms";
	
	/**
	 * The property key for the problems available in the diagnostic tool.
	 */
	public static final String KEY_DIAGNOSTIC_TOOL_PROBLEMS = KEY_PREFIX +
			"analysis.diagnostics.problems";
	
	/**
	 * The property key for the genetic programming protected functions flag.
	 */
	public static final String KEY_GP_PROTECTED_FUNCTIONS = KEY_PREFIX +
			"util.tree.protected_functions";
	
	/**
	 * The property key for the cleanup strategy when restarting from previous
	 * runs.
	 */
	public static final String KEY_CLEANUP_STRATEGY = KEY_PREFIX + 
			"analysis.sensitivity.cleanup";
	
	}
	

