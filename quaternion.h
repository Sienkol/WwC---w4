
#ifndef _QUATMATHVECT__H
#define _QUATMATHVECT__H

#define M_PI 3.14159265358979323846  
#define M_RAD 180/M_PI

#include <math.h>

#ifndef _VECTOR3D_H 
  #include "vector3D.h"
#endif


struct quaternion
{
       float x,y,z,w;

       quaternion(float x1,float y1,float z1,float w1);
       quaternion();

       quaternion AsixAngle();        // zamiana kwaterniona na reprezentacjê k¹towo-osiow¹
       Vector3 obroc_wektor(Vector3 w);      // obrót wektora z u¿yciem kwaterniona obrotu

      quaternion operator*(quaternion q); // iloczyn vectorowy
      quaternion operator~ ();
      quaternion operator+=(quaternion q);  // dodanie vec+vec
      quaternion operator+ (quaternion q);  // dodanie vec+vec
      quaternion operator- (quaternion q);  // odejmowanie vec-vec
      quaternion n(); // licz normal_vector z obecnego kwaternionu 
      float l(); // length kwateriona 
      quaternion operator* (float value); // mnozenie razy skalar
      quaternion operator/ (float value); // dzielenie przez skalar

  
};

quaternion AsixToQuat(Vector3 v,float angle);

#endif
