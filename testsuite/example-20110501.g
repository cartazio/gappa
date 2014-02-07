@rnd = float<ieee_64,ne>;
x = rnd(dummyx); # x is a double

# Cody-Waite argument reduction
Log2h = 0xb.17217f7d1cp-4; # 42 bits out of 53
Log2l = 0xf.79abc9e3b398p-48;
InvLog2 = 0x1.71547652b82fep0;
k = int<ne>(rnd(x*InvLog2));
t1 rnd= x - k*Log2h;
t2 rnd= t1 - k*Log2l;

# exact values
T1 = x - k*Log2h;
T2 = T1 - k*Log2l;

{
  x in [0.3, 800]
->
  t1 = T1 /\
  T1 in [-0.35,0.35] /\
  |t2 - T2| <= 0x1.0001p-55
}

Log2h ~ 1/InvLog2;

# try harder!
T1 $ x;
