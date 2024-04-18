import Game.Metadata.MatrixNotation

open Matrix

#check !![0]
#check !![0,1]
#check !![0,1,2]

#check !![0;0]
#check !![0,1; 2, 3; 4, 5]
#check !![0,1,2; 3, 4, 5]


-- peculiar examples:
#check !![]
#check !![,,,]
#check !![;;;]
