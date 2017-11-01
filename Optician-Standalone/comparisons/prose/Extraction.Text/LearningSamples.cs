using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.ProgramSynthesis.AST;
using Microsoft.ProgramSynthesis.Extraction.Text;
using Microsoft.ProgramSynthesis.Extraction.Text.Constraints;
using Microsoft.ProgramSynthesis.Extraction.Text.Semantics;
using Microsoft.ProgramSynthesis.Utils;
using Microsoft.ProgramSynthesis.Transformation.Text;
using Microsoft.ProgramSynthesis.Transformation.Text.Semantics;
using Microsoft.ProgramSynthesis.Wrangling.Constraints;
using Microsoft.ProgramSynthesis.VersionSpace;
using Microsoft.ProgramSynthesis.Wrangling;
using System.Diagnostics;
using VBFIO = Microsoft.VisualBasic.FileIO;

namespace Extraction.Text
{
    /// <summary>
    ///     Extraction.Text learns programs to extract a single string region or a sequence of string regions from text files.
    ///     This class demonstrates some common usage of Extraction.Text APIs.
    /// </summary>
    internal static class LearningSamples
	{
		private class Result
		{
			public ResultType ResultType { get; set; }
			public long Milliseconds { get; set; }
		}

		private enum ResultType { Success, Exception, IncorrectResponse, NothingLearned }

		private const int NUM_TESTS = 100;

        private static void Main(string[] args)
		{
			if (args.Length != 2)
			{
				throw new Exception(args.Length.ToString());
			}
			var numExamples = int.Parse(args[0]);
			var fileName = args[1];
			var results = GetResults(fileName, numExamples);
			var failedResults = results.Where(result => result.ResultType != ResultType.Success).ToList();
			if (failedResults.IsEmpty())
			{
				Console.Out.WriteLine(results.Select(result => result.Milliseconds).Sum());
			}
			else
			{
				Console.Out.WriteLine(failedResults.First().ResultType);
			}

            // Learning sequence is similar to learning region. 
            // We only illustrate some API usages. Other sequence learning APIs are similar to their region APIs counterpart.
            // Note: we need to give positive examples continuously. 
            // For instance, suppose we learn a list of {A, B, C, D, E}.
            // {A, B} is a valid set of examples, while {A, C} is not.
            // In case of { A, C}, Extraction.Text assumes that B is a negative example. 
            // This helps our learning converge more quickly.
            //LearnSequence();

           /* LearnSequenceReferencingSibling();*/

//            Console.ReadKey();
        }

		private static IList<Tuple<uint, uint>> GetRegions(string region_str)
		{
			if (region_str == "")
			{
				return new List<Tuple<uint, uint>>();
			}
			string[] activeRegionStrings = region_str.Split(';');
			return activeRegionStrings
					.Select((reg_str) =>
						{
							string[] split_region = reg_str.Split(',');
							if (split_region.Length != 2)
							{
								throw new Exception("bad tuple: " + reg_str + " region: " + region_str);
							}
							uint left = uint.Parse(split_region[0]);
							uint right = uint.Parse(split_region[1]);
							if (left > right)
							{
								throw new Exception("bad tuple: " + reg_str + " region: " + region_str);
							}
							return new Tuple<uint, uint>(left, right);
						})
					.ToList();
		}

		private static IDictionary<string, IList<Tuple<string, IList<Tuple<uint, uint>>, IList<Tuple<uint, uint>>>>>
			ParseOutIOList(string fileName)
		{
			var ioList = new List<Tuple<string, string, IList<Tuple<uint,uint>>, IList<Tuple<uint,uint>>>>();

			using (var parser = new VBFIO.TextFieldParser(fileName))
			{
				parser.TextFieldType = VBFIO.FieldType.Delimited;
				parser.SetDelimiters("\t");
				while (!parser.EndOfData)
				{
					string[] fields = parser.ReadFields();
					if (fields.Count() != 4)
					{
						throw new Exception(fields.Count().ToString() + fileName);
					}
					fields = fields.Select(fld =>
										   fld.Replace("\\t", "\t")
										   .Replace("\\n", "\n")
										   .Replace("\\\\", "\\"))
								   .ToArray();
					string problemIdentifier = fields[0];
					string inputString = fields[1];
					string activeRegionString = fields[2];
					string nonActiveRegionString = fields[3];
					IList<Tuple<uint, uint>> activeRegions = GetRegions(activeRegionString);
					IList<Tuple<uint, uint>> nonActiveRegions = GetRegions(nonActiveRegionString);
					ioList.Add(new Tuple<string, string, IList<Tuple<uint, uint>>, IList<Tuple<uint, uint>>>
					           (problemIdentifier, inputString, activeRegions, nonActiveRegions));
				}
			}
			var myDict = new Dictionary<string, IList<Tuple<string, IList<Tuple<uint, uint>>, IList<Tuple<uint, uint>>>>>();
			foreach (var val in ioList)
			{
				string problemIdentifier = val.Item1;
				string inputString = val.Item2;
				IList<Tuple<uint, uint>> activeRegions = val.Item3;
				IList<Tuple<uint, uint>> passiveRegions = val.Item4;
				IList<Tuple<string, IList<Tuple<uint, uint>>, IList<Tuple<uint, uint>>>> specTuples;
				if (!myDict.TryGetValue(val.Item1, out specTuples))
				{
					specTuples = new List<Tuple<string, IList<Tuple<uint, uint>>, IList<Tuple<uint, uint>>>>();
					myDict.Add(problemIdentifier, specTuples);
				}
				specTuples.Add(new Tuple<string, IList<Tuple<uint, uint>>, IList<Tuple<uint, uint>>>
				               (inputString, activeRegions, passiveRegions));
			}
			return myDict;
		}

		private static bool IsOkString(string s)
		{
			return !String.IsNullOrWhiteSpace(s)
				          && !String.IsNullOrEmpty(s)
						  && !Char.IsWhiteSpace(s[s.Length-1])
						  && !Char.IsWhiteSpace(s[0]);
		}

		private static bool IsOkRegion(string s, uint first, uint second)
		{
			return IsOkString(RegionSession.CreateStringRegion(s)
											  .Slice(first, second).ToString());
		}

		private static IEnumerable<Result> GetResults(string fileName, int numExamples)
		{
			var ioList = ParseOutIOList(fileName);
			return ioList.AsEnumerable()
						 .Where(kvp =>
			{
				var testsAndSpecs = kvp.Value;
				var positiveStrings = testsAndSpecs
										.SelectMany(t =>
											t.Item2.Select(fs => RegionSession.CreateStringRegion(t.Item1)
					                                       .Slice(fs.Item1, fs.Item2).ToString()));
				return positiveStrings.Any(s => IsOkString(s));
			})
				         .Select(kvp =>
			{
				var sw = new Stopwatch();
				sw.Start();
				var testsAndSpecs =
					kvp.Value.Select(
						t =>
						new Tuple<string, IList<Tuple<uint, uint>>, IList<Tuple<uint, uint>>>
						(t.Item1,
						 t.Item2.Where(fs => IsOkRegion(t.Item1, fs.Item1, fs.Item2))
						 		.ToList(),
						 t.Item3));
				testsAndSpecs =
					testsAndSpecs.Where(t =>
										t.Item2.Any(fs =>
										{
											return IsOkRegion(t.Item1, fs.Item1, fs.Item2);
										}))
					             .ToList();
				var tests = testsAndSpecs.Take(NUM_TESTS)
				               .ToList();
				var specs = testsAndSpecs.Skip(NUM_TESTS)
				               .Take(numExamples)
				               .ToList();
				var resultType = GenerateProgramAndCollectResult(tests, specs);
				return new Result()
				{
					ResultType = resultType,
					Milliseconds = sw.ElapsedMilliseconds,
				};
			}).ToList();
		}

		private static ResultType GenerateProgramAndCollectResult(
			IList<Tuple<string, IList<Tuple<uint, uint>>, IList<Tuple<uint, uint>>>> tests,
			IList<Tuple<string, IList<Tuple<uint, uint>>, IList<Tuple<uint, uint>>>> specs)
		{
			var session = new SequenceSession();
			foreach (var spec in specs)
			{
				string inputString = spec.Item1;
				StringRegion inputRegion = RegionSession.CreateStringRegion(inputString);
				StringRegion[] positiveRegions =
					spec.Item2.Select(ex_tuple => inputRegion.Slice(ex_tuple.Item1,ex_tuple.Item2))
					    .ToArray();
				var sequencePositiveExamples = new SequenceExample(inputRegion, positiveRegions);
				var sequenceNegativeExamples =
					spec.Item3.Select(ex_tuple => 
					                  new SequenceNegativeExample(
						                  inputRegion,
						                  inputRegion.Slice(ex_tuple.Item1, ex_tuple.Item2))).ToList();
				//Console.WriteLine("a");
				//Console.WriteLine(sequencePositiveExamples);
				session.AddConstraints(sequencePositiveExamples);
				//Console.WriteLine("b");
				//Console.WriteLine(sequenceNegativeExamples);
				session.AddConstraints(sequenceNegativeExamples);
			}
			ResultType result;
			//Console.WriteLine("c");
			var topRankedProgram = session.Learn();
			if (topRankedProgram == null)
			{
				result = ResultType.NothingLearned;
			}
			else if (!tests.All(tuple =>
								{
									var inputRegion = RegionSession.CreateStringRegion(tuple.Item1);
									var results = topRankedProgram.Run(inputRegion)
									                              .ToArray();
									if (results.Length == tuple.Item2.Count)
									{
										for (int i = 0; i < results.Length; i++)
										{
											if (results[i] != inputRegion.Slice(tuple.Item2[i].Item1, tuple.Item2[i].Item2))
											{
												return false;
											}
										}
										return true;
									}
									else
									{
										return false;
									}
								}))
			{
				result = ResultType.IncorrectResponse;
			}
			else
			{
				result = ResultType.Success;
			}

			return result;
/*			ResultType result;
			Program topRankedProgram = Learner.Instance.Learn(constraints);

			if (topRankedProgram == null)
			{
				result = ResultType.NothingLearned;
			}
			else if (!tests.All(kvp =>
								kvp.Value.Equals(topRankedProgram.Run(kvp.Key))))
			{
				Console.WriteLine(tests.Where(kvp => !kvp.Value.Equals(topRankedProgram.Run(kvp.Key))).First().Key);
				Console.WriteLine("first\n\n\nsecond");
				Console.WriteLine(tests.Where(kvp => !kvp.Value.Equals(topRankedProgram.Run(kvp.Key))).First().Value);
				Console.WriteLine("third\n\n\n");
				Console.WriteLine(topRankedProgram.Run(tests.Where(kvp => !kvp.Value.Equals(topRankedProgram.Run(kvp.Key))).First().Key)); Console.WriteLine("\n\n\n");
				result = ResultType.IncorrectResponse;
			}
			else
			{
				result = ResultType.Success;
			}

			return result;*/
		}

        /// <summary>
        ///     Learns a program to extract a region with both positive and negative examples.
        ///     Demonstrates the use of negative examples.
        /// </summary>
        private static void LearnRegionWithNegativeExamples()
        {
            var session = new RegionSession();
            StringRegion input =
                RegionSession.CreateStringRegion("Carrie Dodson 100\nLeonard Robledo NA\nMargaret Cook 320");
            StringRegion[] records = { input.Slice(0, 17), input.Slice(18, 36), input.Slice(37, 54) };

            // Suppose we want to extract "100", "320".
            session.AddConstraints(
                new RegionExample(records[0], records[0].Slice(14, 17)), // "Carrie Dodson 100" => "100"
                new RegionNegativeExample(records[1], records[1]) // no extraction in "Leonard Robledo NA"
            );

            // Extraction.Text will find a program whose output does not OVERLAP with any of the negative examples.
            RegionProgram topRankedProg = session.Learn();
            if (topRankedProg == null)
            {
                Console.Error.WriteLine("Error: Learning fails!");
                return;
            }

            foreach (StringRegion record in records)
            {
                string output = topRankedProg.Run(record)?.Value ?? "null";
                Console.WriteLine("\"{0}\" => \"{1}\"", record, output);
            }
        }

        /// <summary>
        ///     Learns a program to extract a sequence of regions from a file.
        /// </summary>
        private static void LearnSequence()
        {
            var session = new SequenceSession();
            // It is advised to learn a sequence with at least 2 examples because generalizing a sequence from a single element is hard.
            // Also, we need to give positive examples continuously (i.e., we cannot skip any example).
            var input =
                SequenceSession.CreateStringRegion(
                    "United States\n Carrie Dodson 100\n Leonard Robledo 75\n Margaret Cook 320\n" +
                    "Canada\n Concetta Beck 350\n Nicholas Sayers 90\n Francis Terrill 2430\n" +
                    "New Zealand\n Nettie Pope 50\n Mack Beeson 1070" +
				"\n Lameo Magamo\n Imot Lame\n Shut it");
            // Suppose we want to extract all last names from the input string.
            session.AddConstraints(
                new SequenceExample(input, new[]
                {
                    input.Slice(15, 21), // input => "Carrie"
                    input.Slice(34, 41), // input => "Leonard"
                })
			);
			session.AddConstraints(
				new SequenceNegativeExample(input, input.Slice(187,199))
			);
            SequenceProgram topRankedProg = session.Learn();
            if (topRankedProg == null)
            {
                Console.Error.WriteLine("Error: Learning fails!");
                return;
            }

            foreach (StringRegion r in topRankedProg.Run(input))
            {
                string output = r != null ? r.Value : "null";
                Console.WriteLine(output);
            }
        }
    }
}
