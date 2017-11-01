using System;
using System.IO;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Security.Permissions;
using Microsoft.ProgramSynthesis.Transformation.Text;
using Microsoft.ProgramSynthesis.Transformation.Text.Semantics;
using Microsoft.ProgramSynthesis.Wrangling.Constraints;
using VBFIO = Microsoft.VisualBasic.FileIO;
using System.Diagnostics;

namespace Transformation.Text
{
	/// <summary>
	///     Sample of how to use the Transformation.Text API. Transformation.Text generates string programs from input/output examples.
	/// </summary>
	internal static class SampleProgram
	{
		private enum ResultType { Success, Exception, IncorrectResponse, NothingLearned }

		private const int NUM_TESTS = 100;

		private static void Main(string[] args)
		{
			var t = new Stopwatch();
			if (args.Length != 2) {
				throw new Exception(args.Length.ToString());
			}
			var numExamples = int.Parse(args[0]);
			var fileName = args[1];
			t.Start();
			var result = GetResult(fileName, numExamples);
			if (result == ResultType.Success)
			{
				t.Stop();
				Console.Out.WriteLine(t.ElapsedMilliseconds);
			}
			else
			{
				Console.Out.WriteLine(GetResult(fileName, numExamples).ToString());
			}
		}

		private static List<KeyValuePair<string, string>> ParseOutIOList(string fileName)
		{
			var ioList = new List<KeyValuePair<string, string>>();
/*			var reader = new StreamReader(fileName);
			var csv = new CsvReader(reader);
			csv.Configuration.Delimiter = "\t";
			csv.Configuration.HasHeaderRecord = false;
			while (csv.Read())
			{
				ioList.Add(new KeyValuePair<string,string>(csve.GetField<string>(0),csv.GetField<string>(1)));
				Console.Out.WriteLine("in");
				Console.Out.WriteLine(csv.GetField<string>(0));
				Console.Out.WriteLine("out");
				Console.Out.WriteLine(csv.GetField<string>(1));
			}
			Console.Out.WriteLine(ioList.Count());
			Console.Out.WriteLine(fileName);
			return ioList;*/

			using (var parser = new VBFIO.TextFieldParser(fileName))
			{
				parser.TextFieldType = VBFIO.FieldType.Delimited;
				parser.SetDelimiters("\t");
				while (!parser.EndOfData)
				{
					string[] fields = parser.ReadFields();
					if (fields.Count() != 2)
					{
						throw new Exception(fields.Count().ToString() + fileName);
					}
					fields = fields.Select(fld =>
										   fld.Replace("\\t", "\t")
					                       .Replace("\\n", "\n")
					                       .Replace("\\\\", "\\"))
					               .ToArray();
					ioList.Add(new KeyValuePair<string, string>(fields[0], fields[1]));
				}
			}
			return ioList;
		}

		private static ResultType GetResult(string fileName, int numExamples)
		{
			var ioList = ParseOutIOList(fileName);
			var irowOutputList = ioList.Select(kvp =>
			                                   new KeyValuePair<IRow, string>(new InputRow(kvp.Key), kvp.Value))
			                           .ToList();
			var tests = irowOutputList.Take(NUM_TESTS);
			var constraints = irowOutputList.Skip(NUM_TESTS)
			                        		.Take(numExamples)
											.Select(kvp =>
			                                		new Example(kvp.Key, kvp.Value));
			ResultType result = GenerateProgramAndCollectResult(constraints, tests);
			return result;
		}

		private static ResultType GenerateProgramAndCollectResult(
			IEnumerable<Constraint<IRow, object>> constraints, IEnumerable<KeyValuePair<IRow, string>> tests)
		{
			ResultType result;
			Program topRankedProgram = Learner.Instance.Learn(constraints);

			if (topRankedProgram == null)
			{
				result = ResultType.NothingLearned;
			}
			else if (!tests.All(kvp =>
			                    kvp.Value.Equals(topRankedProgram.Run(kvp.Key))))
			{
				/*Console.WriteLine(tests.Where(kvp => !kvp.Value.Equals(topRankedProgram.Run(kvp.Key))).First().Key);
				Console.WriteLine("first\n\n\nsecond");
				Console.WriteLine(tests.Where(kvp => !kvp.Value.Equals(topRankedProgram.Run(kvp.Key))).First().Value);
				Console.WriteLine("third\n\n\n");
				Console.WriteLine(topRankedProgram.Run(tests.Where(kvp => !kvp.Value.Equals(topRankedProgram.Run(kvp.Key))).First().Key)); Console.WriteLine("\n\n\n");*/
				result = ResultType.IncorrectResponse;
			}
			else
			{
				result = ResultType.Success;
			}

			return result;
		}
    }
}
