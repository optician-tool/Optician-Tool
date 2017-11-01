# Main Changes to Old Boomerang Code

* Added two new constructs for regular expressions i.e. perm and var. The perm construct is a shorthand for a BIG permutation regular expression. The var construct is used during synthesis.

* Added a var construct for lenses that is used during synthesis. Added two new fields for lenses vtype and stype which are used in populating the lenscontext with lenses that have source and view types which are variables.

* Changed the refinement type to have an optional pair of expressions. The new pair is used to populate the (new) vtype and stype fields for lenses.

* Added three new expression types i.e. perm, project, id and synth. The first three are qre's, and the last is used for synthesis.

# Tasks in Progress

* All the synthesis tasks in the lensynthexamples folder except for the three tasks in aug/xml.boom complete successfully.

* A new construct that builds a nested perm canonizer from a string e.g.
```
xml_to_perm "library={name, address, books={book={title,genre,author={name,age,nationality}}}, department}"

```

# Tasks for Which I am not sure how to proceed

* The syntax for defining qre's is not so nice e.g

```
perm #{canonizer}[id xmlname; id xmldate; id xmlgenres; id xmladdress] with
                (project wsp* -> "\n")
```

should really be
```
perm [xmlname; xmldate; xmlgenres; xmladdress] with (project wsp* -> "\n")
```

Also the syntax for synthesis is not so nice e.g
```
synth A <=> B with #{string * string}[]
```
should really be
```
synth A <=> B
```

Should I go around using boomerang lists or hack them? Hacking them is difficult since the list module is not part of standard boomerang. On the other hand, I would have to change the parser to go around boomerang lists, which I will probably need help with.


