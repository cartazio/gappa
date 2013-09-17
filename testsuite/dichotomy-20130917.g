@rnd = float<ieee_32,ne>;
x = rnd(x_);
y rnd= x * (1 - x);

{ x in [0,1] -> y in ? /\ y - x * (1 - x) in [-3b-27,3b-27] }

x * (1 - x) ->  0.25 - (x - 0.5) * (x - 0.5);
y - x * (1 - x) $ x;
