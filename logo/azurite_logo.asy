settings.outformat = "svg";

unitsize(1mm);

pair p1 = (457.9816, -75.2562);
pair p2 = (259.1551, -38.5159);
pair p3 = (349.0400, -20.4697);
pair p4 = (191.0107, -78.5139);
pair p5 = (293.7875, -97.0097);
pair p6 = (273.0741, -230.0461);
pair p7 = (117.4699, -133.3493);
pair p8 = (153.1031, -187.3543);
pair p9 = (152.0109, -337.4948);
pair p10 = (32.6856, -277.6116);
pair p11 = (56.4942, -309.1929);
pair p12 = (87.8317, -465.6232);
pair p13 = (26.3253, -437.1918);
pair p14 = (94.9062, -586.7142);
pair p15 = (155.9053, -655.4088);
pair p16 = (314.4491, -548.7118);
pair p17 = (291.3746, -389.1543);
pair p18 = (188.9660, -597.9215);
pair p19 = (337.0322, -674.3408);
pair p20 = (223.4928, -694.2483);
pair p21 = (309.0429, -732.6201);
pair p22 = (513.8502, -36.0177);
pair p23 = (648.6095, -122.1075);
pair p24 = (609.5519, -126.2787);
pair p25 = (536.8157, -195.8659);
pair p26 = (422.6506, -290.0097);
pair p27 = (667.8715, -271.5851);
pair p28 = (730.8640, -265.2600);
pair p29 = (742.2553, -358.0725);
pair p30 = (742.3110, -436.1639);
pair p31 = (675.0697, -438.0797);
pair p32 = (713.0039, -523.8874);
pair p33 = (610.8995, -591.2127);
pair p34 = (617.4967, -658.7683);
pair p35 = (477.5018, -732.5679);
pair p36 = (490.4297, -697.1073);
pair p37 = (468.5937, -599.0087);
pair p38 = (569.7842, -354.4346);
pair p39 = (443.5291, -452.7418);

pen[] colors = new pen [] {
    RGB(89, 169, 231),   // [0]  #59a9e7  light
    RGB(41, 109, 198),   // [1]  #296dc6  medium (= wordmark)
    RGB(30, 61, 131),    // [2]  #1e3d83  dark
    RGB(18, 29, 55)      // [3]  #121d37  darkest
};

// Faces are grouped by orbit under the 3-fold rotation about the polyhedron's
// center. Every face in an orbit maps onto the others under a 120 deg turn, so
// give all fills in one orbit the same colors[i] to keep the logo symmetric.

// orbit 1: central triangle (fixed by the rotation)
fill(p26 -- p39 -- p17 -- cycle, colors[3]);

// orbit 2: 3 triangles, ring r~93
fill(p6 -- p26 -- p17 -- cycle, colors[0]);
fill(p26 -- p38 -- p39 -- cycle, colors[0]);
fill(p17 -- p39 -- p16 -- cycle, colors[0]);

// orbit 3: 3 triangles, ring r~158
fill(p6 -- p17 -- p9 -- cycle, colors[1]);
fill(p25 -- p38 -- p26 -- cycle, colors[1]);
fill(p16 -- p39 -- p37 -- cycle, colors[1]);

// orbit 4: 3 pentagons, ring r~200
fill(p25 -- p26 -- p6 -- p5 -- p1 -- cycle, colors[2]);
fill(p37 -- p39 -- p38 -- p31 -- p33 -- cycle, colors[2]);
fill(p16 -- p18 -- p12 -- p9 -- p17 -- cycle, colors[2]);

// orbit 5: 3 triangles, ring r~230
fill(p6 -- p9 -- p8 -- cycle, colors[0]);
fill(p25 -- p27 -- p38 -- cycle, colors[0]);
fill(p16 -- p37 -- p19 -- cycle, colors[0]);

// orbit 6: 3 triangles, ring r~252
fill(p6 -- p8 -- p5 -- cycle, colors[1]);
fill(p27 -- p31 -- p38 -- cycle, colors[1]);
fill(p16 -- p19 -- p18 -- cycle, colors[1]);

// orbit 7: 3 triangles, ring r~283
fill(p9 -- p11 -- p8 -- cycle, colors[1]);
fill(p24 -- p27 -- p25 -- cycle, colors[1]);
fill(p19 -- p37 -- p36 -- cycle, colors[1]);

// orbit 8: 3 triangles, ring r~287
fill(p9 -- p12 -- p11 -- cycle, colors[0]);
fill(p1 -- p24 -- p25 -- cycle, colors[0]);
fill(p36 -- p37 -- p33 -- cycle, colors[0]);

// orbit 9: 3 triangles, ring r~309
fill(p4 -- p5 -- p8 -- cycle, colors[3]);
fill(p29 -- p31 -- p27 -- cycle, colors[3]);
fill(p19 -- p20 -- p18 -- cycle, colors[3]);

// orbit 10: 3 triangles, ring r~314
fill(p1 -- p5 -- p3 -- cycle, colors[1]);
fill(p31 -- p32 -- p33 -- cycle, colors[1]);
fill(p12 -- p18 -- p14 -- cycle, colors[1]);

// orbit 11: 3 triangles, ring r~330
fill(p3 -- p5 -- p4 -- cycle, colors[0]);
fill(p29 -- p32 -- p31 -- cycle, colors[0]);
fill(p14 -- p18 -- p20 -- cycle, colors[0]);

// orbit 12: 3 triangles, ring r~330
fill(p22 -- p24 -- p1 -- cycle, colors[1]);
fill(p34 -- p36 -- p33 -- cycle, colors[1]);
fill(p11 -- p12 -- p13 -- cycle, colors[1]);

// orbit 13: 3 pentagons, ring r~329
fill(p8 -- p11 -- p10 -- p7 -- p4 -- cycle, colors[2]);
fill(p23 -- p28 -- p29 -- p27 -- p24 -- cycle, colors[2]);
fill(p19 -- p36 -- p35 -- p21 -- p20 -- cycle, colors[2]);

// orbit 14: 3 triangles, ring r~338
fill(p1 -- p3 -- p22 -- cycle, colors[0]);
fill(p32 -- p34 -- p33 -- cycle, colors[0]);
fill(p12 -- p14 -- p13 -- cycle, colors[0]);

// orbit 15: 3 triangles, ring r~349
fill(p10 -- p11 -- p13 -- cycle, colors[3]);
fill(p23 -- p24 -- p22 -- cycle, colors[3]);
fill(p34 -- p35 -- p36 -- cycle, colors[3]);

// orbit 16: 3 triangles, ring r~352
fill(p2 -- p3 -- p4 -- cycle, colors[1]);
fill(p30 -- p32 -- p29 -- cycle, colors[1]);
fill(p14 -- p20 -- p15 -- cycle, colors[1]);

