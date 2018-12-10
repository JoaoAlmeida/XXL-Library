/* XXL: The eXtensible and fleXible Library for data processing

Copyright (C) 2000-2004 Prof. Dr. Bernhard Seeger
                        Head of the Database Research Group
                        Department of Mathematics and Computer Science
                        University of Marburg
                        Germany

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307,
USA

	http://www.xxl-library.de

bugs, requests for enhancements: request@xxl-library.de

If you want to be informed on new versions of XXL you can 
subscribe to our mailing-list. Send an email to 
	
	xxl-request@lists.uni-marburg.de

without subject and the word "subscribe" in the message body. 
*/

package xxl.core.io.converters;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;

/**
 * This class provides a converter that is able to read and write arrays
 * of <tt>int</tt> values. First the converter reads or writes the length
 * of the <tt>int</tt> array. Thereafter the <tt>int</tt> values are read
 * or written.<p>
 *
 * Example usage (1).
 * <pre>
 *     // create an int array
 *
 *     int [] array = {42, 4711, 666, 190, 77};
 *
 *     // catch IOExceptions
 *
 *     try {
 *
 *         // create a byte array output stream
 *
 *         ByteArrayOutputStream output = new ByteArrayOutputStream();
 *
 *         // write array to the output stream
 *
 *         IntegerArrayConverter.DEFAULT_INSTANCE.write(new DataOutputStream(output), array);
 *
 *         // create a byte array input stream on the output stream
 *
 *         ByteArrayInputStream input = new ByteArrayInputStream(output.toByteArray());
 *
 *         // reset the array
 *
 *         array = null;
 *
 *         // read array from the input stream
 *
 *         array = (int[])IntegerArrayConverter.DEFAULT_INSTANCE.read(new DataInputStream(input));
 *
 *         // print the array
 *
 *         for (int i = 0; i < array.length; i++)
 *             System.out.println(array[i]);
 *
 *         // close the streams after use
 *
 *         input.close();
 *         output.close();
 *     }
 *     catch (IOException ioe) {
 *         System.out.println("An I/O error occured.");
 *     }
 * </pre>
 *
 * @see DataInput
 * @see DataOutput
 * @see IOException
 */
public class IntegerArrayConverter extends SizeConverter {

	/**
	 * This instance can be used for getting a default instance of
	 * IntegerArrayConverter. It is similar to the <i>Singleton Design
	 * Pattern</i> (for further details see Creational Patterns, Prototype
	 * in <i>Design Patterns: Elements of Reusable Object-Oriented
	 * Software</i> by Erich Gamma, Richard Helm, Ralph Johnson, and John
	 * Vlissides) except that there are no mechanisms to avoid the
	 * creation of other instances of IntegerArrayConverter.
	 */
	public static final IntegerArrayConverter DEFAULT_INSTANCE = new IntegerArrayConverter();

	/**
	 * Determines the length of the conversion of an int array.
	 * @param withLengthInfo has to be true iff the length info of the array has to be stored.
	 * @param length length of the array to be stored.
	 * @return length in bytes
	 */
	public static int getSizeForArray(boolean withLengthInfo, int length) {
		if (withLengthInfo)
			return 4+4*length;
		else
			return 4*length;
	}
	
	/** 
	 * Determines the length of the array. If it is -1, then the 
	 * size information is also serialized.
	 */
	protected int arraySize;

	/**
	 * Constructors a IntegerArrayConverter which not necessarily serializes/deserializes the 
	 * length of the array.
	 * @param arraySize if -1 then the size is not serialized/deserialized. Else this
	 *	int value represents the number of elements which are serialized/deserialized.
	 */
	public IntegerArrayConverter(int arraySize) {
		this.arraySize = arraySize;
	}

	/**
	 * Constructors a IntegerArrayConverter which also serializes/deserializes the 
	 * length of the array.
	 */
	public IntegerArrayConverter() {
		this(-1);
	}

	/**
	 * Reads an array of <tt>int</tt> values from the specified data input
	 * and returns the restored <tt>int</tt> array. <br>
	 * This implementation ignores the specified <tt>int</tt> array and
	 * returns a new array of <tt>int</tt> values. So it does not matter
	 * when the specified array is <tt>null</tt>.
	 *
	 * @param dataInput the stream to read the <tt>int</tt> array from.
	 * @param object the <tt>int</tt> array to be restored. In this
	 *        implementation it is ignored.
	 * @return the read array of <tt>int</tt> values.
	 * @throws IOException if I/O errors occur.
	 */
	public Object read (DataInput dataInput, Object object) throws IOException {
		int [] array;
		if (arraySize==-1)
			array = new int[dataInput.readInt()];
		else
			array = new int[arraySize];

		for (int i=0; i<array.length; i++)
			array[i] = dataInput.readInt();
		return array;
	}

	/**
	 * Writes the specified array of <tt>int</tt> values to the specified
	 * data output. <br>
	 * This implementation first writes the length of the array to the
	 * data output. Thereafter the <tt>int</tt> values are written.
	 *
	 * @param dataOutput the stream to write the <tt>int</tt> array to.
	 * @param object the <tt>int</tt> array that should be written to the
	 *        data output.
	 * @throws IOException includes any I/O exceptions that may occur.
	 */
	public void write (DataOutput dataOutput, Object object) throws IOException {
		int [] array = (int [])object;
		int len = arraySize;
		
		if (arraySize==-1) {
			dataOutput.writeInt(array.length);
			len = array.length;
		}
		for (int i=0; i<len; i++)
			dataOutput.writeInt(array[i]);
	}

	/**
	 * Determines the size of the int array in bytes.
	 * @param o int array
	 * @return the size in bytes
	 * @see xxl.core.io.converters.SizeConverter#getSerializedSize(java.lang.Object)
	 */
	public int getSerializedSize(Object o) {
		int [] array = (int [])o;
		if (arraySize==-1)
			return getSizeForArray(true, array.length);
		else
			return getSizeForArray(false, arraySize);
	}

	/**
	 * The main method contains some examples how to use an
	 * IntegerArrayConverter. It can also be used to test the
	 * functionality of an IntegerArrayConverter.
	 *
	 * @param args array of <tt>String</tt> arguments. It can be used to
	 *        submit parameters when the main method is called.
	 */
	public static void main (String [] args) {

		//////////////////////////////////////////////////////////////////
		//                      Usage example (1).                      //
		//////////////////////////////////////////////////////////////////

		// create an int array
		int [] array = {42, 4711, 666, 190, 77};
		// catch IOExceptions
		try {
			System.out.println("Converts an array of 5 ints");
			// create a byte array output stream
			java.io.ByteArrayOutputStream output = new java.io.ByteArrayOutputStream();
			// write array to the output stream
			IntegerArrayConverter.DEFAULT_INSTANCE.write(new java.io.DataOutputStream(output), array);
			// create a byte array input stream on the output stream
			java.io.ByteArrayInputStream input = new java.io.ByteArrayInputStream(output.toByteArray());
			// reset the array
			array = null;
			// read array from the input stream
			array = (int[])IntegerArrayConverter.DEFAULT_INSTANCE.read(new java.io.DataInputStream(input));
			// print the array
			for (int i = 0; i<array.length; i++)
				System.out.println(array[i]);
			// close the streams after use
			input.close();
			output.close();
		}
		catch (IOException ioe) {
			throw new xxl.core.util.WrappingRuntimeException(ioe);
		}
	}
}
