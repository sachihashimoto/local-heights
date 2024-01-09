# local-heights
Code for "Local heights on hyperelliptic curves and quadratic Chabauty" by L. Alexander Betts, Juanita Duque-Rosero, Sachi Hashimoto, and Pim Spelier.

This code computes local heights h_ell for ell not equal to p on hyperelliptic curves of the form y^2 = f, where f is monic and even degree. Some examples for how to use the code can be found in the examples folder.

Prerequisites:

Magma (this code has been tested on Magma V2.27-1 and V2.28-3).

The Endomorphisms package, available at https://github.com/edgarcosta/endomorphisms or through https://github.com/edgarcosta/chimp

To run the quadratic Chabauty rational points computation, one also needs https://github.com/steffenmueller/QCMod