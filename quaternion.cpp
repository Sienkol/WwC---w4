/************************************************************************************************** 
    Obs³uga kwaternionów 
   
    Aby zrealizowaæ obrót nale¿y pomno¿yæ quaternion orientacji przez kwaterion obrotu
    z lewej strony:
            
    qOrient = qRot*qOrient
    
    Uwaga! Zak³adam, ¿e kwaterniony qRot i qOrient s¹ d³ugoœci 1, inaczej trzeba jeszcze je normalizowaæ            
    
    Kwaternion mo¿e tez reprezentowaæ orientacjê obiektu, jeœli za³o¿ymy jak¹œ orientacjê
    pocz¹tkow¹ np. obiekt skierowany w kierunku osi 0x, z normaln¹ zgodn¹ z 0y. Wówczas 
    quaternion odpowiada obrotowi od po³o¿enia poc¿¹tkowego. 
****************************************************************************************************/
#include <stdlib.h>
//#include "vector3D.h"
#include "quaternion.h"


quaternion::quaternion(float x,float y,float z,float w)

{
	this->x=x;
	this->y=y;
	this->z=z;
	this->w=w;
}


quaternion::quaternion()
{
	x=0;
	y=0;
	z=0;
	w=1;
}

// mno¿enie dwóch kwaternionów
quaternion quaternion::operator*(quaternion q)
{
    double rx, ry, rz, rw;		// temp result	


	
	rx	= x*q.w + w*q.x - z*q.y + y*q.z;
	ry	= y*q.w + w*q.y - x*q.z + z*q.x;
	rz	= z*q.w + w*q.z - y*q.x + x*q.y;
	
	rw	= w*q.w - x*q.x - y*q.y - z*q.z;

	return quaternion((float)rx,(float)ry,(float)rz,(float)rw);
}

// zamiana kwaterniona na reprezentacjê k¹towo-osiow¹
// dla wygody oœ i k¹t obrotu umieszczane s¹ w strukturze typu quaternion 
quaternion quaternion::AsixAngle()
{
    Vector3 v(x,y,z);

    if (v.length()==0) return quaternion(0,0,0,1);
    else 
    {
        v=v.znorm();
		    float kat_obrotu = (w <= -1 ? 0 : (w >= 1 ? 0 : 2.0*acos(w)));
        return quaternion(v.x,v.y,v.z,kat_obrotu);
    }
}

quaternion quaternion::operator~ ()
{
    return quaternion(-x,-y,-z,w);
}
  
quaternion quaternion:: operator+= (quaternion q)	// operator+= is used to add another Vector3D to this Vector3D.
{
	x += q.x;
	y += q.y;
	z += q.z;
	w += q.w;
    return *this;
}

quaternion quaternion:: operator+ (quaternion q)	// operator+= is used to add another Vector3D to this Vector3D.
{
        return quaternion(x+q.x,y+q.y,z+q.z,w+q.w);
}
  
quaternion quaternion:: operator- (quaternion q)	// operator+= is used to add another Vector3D to this Vector3D.
{
        return quaternion(x-q.x,y-q.y,z-q.z,w-q.w);
}  
  
quaternion quaternion::n() // licz normal_vector z obecnego wektora
{
float length;

	length=sqrt(x*x+y*y+z*z+w*w);
	if (length==0) return quaternion(0,0,0,0);
	    else return quaternion(x/length,y/length,z/length,w/length);
}

float quaternion::l() // d³ugoœæ 
{
  return sqrt(x*x+y*y+z*z+w*w);
}	

quaternion quaternion::operator* (float value)  // mnozenie razy skalar
{
	return quaternion(x*value,y*value,z*value,w*value);
}

quaternion quaternion::operator/ (float value)  // dzielenie przez skalar
{
	return quaternion(x/value,y/value,z/value,w/value);
}
	


/*  obrót wektora z u¿yciem kwaterniona obrotu - do sprawdzenia
macierz obrotu:
M =  [ w^2 + x^2 - y^2 - z^2       2xy - 2wz                   2xz + 2wy
       2xy + 2wz                   w^2 - x^2 + y^2 - z^2       2yz - 2wx
       2xz - 2wy                   2yz + 2wx                   w^2 - x^2 - y^2 + z^2 ]
*/
Vector3 quaternion::obroc_wektor(Vector3 V)       
{ 
    Vector3 Vo;

    quaternion p = quaternion(V.x,V.y,V.z,0);
    quaternion q = quaternion(x,y,z,w);
    quaternion pp = q*p*~q;
    Vo.x = pp.x;Vo.y = pp.y; Vo.z = pp.z;

    return Vo;    
}

// zamiana obrotu wyra¿onego reprezentacj¹ k¹towo-osiow¹ na reprezentacjê kwaternionow¹  
quaternion AsixToQuat(Vector3 v, float angle)
{
    float x,y,z,w;			// temp vars of vector
    double rad, scale;		// temp vars

	if (v.length()==0) return quaternion();
	
	v = v.znorm();
	rad = angle;
	scale = sin(rad/2.0);


	w = (float)cos(rad/2.0);

	x = float(v.x * scale);
	y = float(v.y * scale);
	z = float(v.z * scale);

	return quaternion(x,y,z,w);
}
