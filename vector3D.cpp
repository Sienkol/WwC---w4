/*
    Operacje na wektorach 3- wymiarowych
*/
#include <math.h>
#include <stdio.h>
#include "vector3D.h"
//#define float double

float pii = 3.14159265358979;

Vector3::Vector3(float x,float y,float z)
{
	this->x=x;
	this->y=y;
	this->z=z;
}

Vector3::Vector3()
{
	x=0;
	y=0;
	z=0;
}

Vector3 Vector3::operator* (float constant)  // mnozenie przez value
{
  return Vector3(x*constant,y*constant,z*constant);
}


Vector3 Vector3::operator/ (float constant)			// operator* is used to scale a Vector3D by a value. This value multiplies the Vector3D's x, y and z.
{
  if (constant!=0)
    return Vector3(x/constant,y/constant,z/constant);
  else return Vector3(x,y,z);
}

Vector3 Vector3::operator+ (float constant)  // dodanie vec+vec
{
  return Vector3(x+constant,y+constant,z+constant);
};


Vector3 Vector3::operator+=(float constant)  // dodanie vec+vec
{
  x += constant;
  y += constant;
  z += constant;
  return *this;
};

Vector3 Vector3:: operator+= (Vector3 ww)			// operator+= is used to add another Vector3D to this Vector3D.
{
  x += ww.x;
  y += ww.y;
  z += ww.z;
  return *this;
}



Vector3 Vector3::operator+ (Vector3 ww)  // dodanie vec+vec
{
  return Vector3(x+ww.x,y+ww.y,z+ww.z);
};


Vector3 Vector3::operator-=(Vector3 ww)  // dodanie vec+vec
{
  x -= ww.x;
  y -= ww.y;
  z -= ww.z;
  return *this;
};

Vector3 Vector3::operator- (Vector3 ww)  // dodanie vec+vec
{
  return Vector3(x-ww.x,y-ww.y,z-ww.z);
};

Vector3 Vector3::operator- ()             // znak (-)
{
  return Vector3(-x,-y,-z);
};

Vector3 Vector3::operator*(Vector3 ww)
{
   Vector3 w;
   w.x=y*ww.z-z*ww.y;
   w.y=z*ww.x-x*ww.z;
   w.z=x*ww.y-y*ww.x;
   return w;
}

bool Vector3::operator==(Vector3 v2)
{
  return (x==v2.x)&&(y==v2.y)&&(z==v2.z);
}

Vector3 Vector3::obrot(float wheel_turn_angle,float vn0,float vn1,float vn2)
{
  float s = sin(wheel_turn_angle), c = cos(wheel_turn_angle);

  Vector3 w;
  w.x = x*(vn0*vn0+c*(1-vn0*vn0)) + y*(vn0*vn1*(1-c)-s*vn2) + z*(vn0*vn2*(1-c)+s*vn1);
  w.y = x*(vn1*vn0*(1-c)+s*vn2) + y*(vn1*vn1+c*(1-vn1*vn1)) + z*(vn1*vn2*(1-c)-s*vn0);
  w.z = x*(vn2*vn0*(1-c)-s*vn1) + y*(vn2*vn1*(1-c)+s*vn0) + z*(vn2*vn2+c*(1-vn2*vn2));

  return w;
}

Vector3 Vector3::obrot(float wheel_turn_angle,Vector3 os)
{
  float s = sin(wheel_turn_angle), c = cos(wheel_turn_angle);

  float vn0 = os.x, vn1 = os.y, vn2 = os.z;
  Vector3 w;
  w.x = x*(vn0*vn0+c*(1-vn0*vn0)) + y*(vn0*vn1*(1-c)-s*vn2) + z*(vn0*vn2*(1-c)+s*vn1);
  w.y = x*(vn1*vn0*(1-c)+s*vn2) + y*(vn1*vn1+c*(1-vn1*vn1)) + z*(vn1*vn2*(1-c)-s*vn0);
  w.z = x*(vn2*vn0*(1-c)-s*vn1) + y*(vn2*vn1*(1-c)+s*vn0) + z*(vn2*vn2+c*(1-vn2*vn2));

  return w;
}

Vector3 Vector3::znorm()
{
  float d = length();
  if (d > 0)
    return Vector3(x/d,y/d,z/d);
  else
    return Vector3(0,0,0);       
}         

Vector3 Vector3::znorm2D()
{
  float d_kw = x*x+y*y;
  float d = (d_kw > 0 ? sqrt(d_kw) : 0);       
  return Vector3(x/d,y/d,0);       
}   

float Vector3::operator^(Vector3 w) // iloczyn skalarny
{
	return w.x*x+w.y*y+w.z*z;
}

float Vector3::length() // length aktualnego wektora
{
  float kw = x*x+y*y+z*z;
  return (kw>0 ? sqrt(kw) : 0);
}


// ****************************
//       DODATKI
//*****************************


// Funkcja obliczajaca normal_vector do plaszczyzny wyznaczanej przez trojkat ABC
// zgodnie z ruchem wskazowek zegara:
Vector3 normal_vector(Vector3 A,Vector3 B, Vector3 C)
{
  Vector3 w1 = B-A, w2 = C-A;
  return (w1*w2).znorm();
}

// rzut prostopadly punktu A na plaszczyzne o normalnej N (o dlugosci 1) i punkcie P:  (4 mnozenia)
Vector3 rzut_punktu_na_pl(Vector3 A, Vector3 N, Vector3 P)
{
  float x = N^(A-P);   // odleglosc punktu A od plaszczyzny ze znakiem
  return A - N*x;
}

// rzut prostopadly punktu P na prosta wyznaczona przez punkty A, B
Vector3 rzut_punktu_na_prosta(Vector3 P, Vector3 A, Vector3 B)
{
  //Vector3 N = ((A-B)*((A-B)*(A-P))).znorm();   // normal_vector plaszcz prostop. do kierunku rzutu
  //return rzut_punktu_na_pl(P,N,A);
	float ilo_skal = (B - A) ^ (B - A);
	if (ilo_skal == 0) // punkty A i B pokrywaj¹ siê
		return A;
	else
		return A + (B - A)*((B - A) ^ (P - A)) / ilo_skal;
}

// najbli¿szy punkt le¿¹cy na odcinku AB do punktu P:
Vector3 najblizszy_punkt_na_odcinku(Vector3 P, Vector3 A, Vector3 B)
{
	Vector3 R = rzut_punktu_na_prosta(P, A, B);
	float ilo_skal = (R - A) ^ (R - B);
	if (ilo_skal > 0)                            // jeœli iloczyn sklarny dodatni, to znaczy, ¿e wektory tak samo skierowane, czyli 
	{                                            // rzut punktu P poza odcinkiem. W tej sytuacji najbli¿szym punktem jest A lub B
		float odl_RA = (R - A).length(), odl_RB = (R - B).length();
		return (odl_RA < odl_RB ? A : B);
	}
	else
		return R;
}


// odleglosc pomiêdzy punktem P a prost¹ wyznaczana przez punkty A,B
float odleglosc_pom_punktem_a_prosta(Vector3 P, Vector3 A, Vector3 B)
{
  /*float l = B.x - A.x, m = B.y - A.y, n = B.z - A.z;
  float liczba1 = (P.x - A.x)*m - (P.y - A.y)*l, liczba2 = (P.y - A.y)*n - (P.z - A.z)*m, liczba3 = (P.z - A.z)*l - (P.x - A.x)*n;
  float sigma = (liczba1*liczba1 + liczba2*liczba2 + liczba3*liczba3)/(l*l + m*m + n*n);
  if (sigma == 0) return 0;
  else return sqrt(sigma);
  */
	Vector3 R = rzut_punktu_na_prosta(P, A, B);
	return (R - P).length();
}

// ró¿ni siê od poprzedniej funkcji tym, ¿e jest ograniczona do odcinka, czyli jeœli
// rzut punktu le¿y poza odcinkiem to wynikiem jest odleg³oœæ do najbli¿szego punktu ze zb. {A,B}
float odleglosc_pom_punktem_a_odcinkiem(Vector3 P, Vector3 A, Vector3 B)
{
	Vector3 R = rzut_punktu_na_prosta(P, A, B);
	float ilo_skal = (R - A) ^ (R - B);
	if (ilo_skal > 0)                            // jeœli iloczyn sklarny dodatni, to znaczy, ¿e wektory tak samo skierowane, czyli 
	{                                            // rzut punktu P poza odcinkiem
		float odl_PA = (P - A).length(), odl_PB = (P - B).length();
		return (odl_PA < odl_PB ? odl_PA : odl_PB);
	}
	else
		return (R - P).length();
}

// odleglosc punktu A od plaszczyzny o normalnej N (o d³ugoœci 1) i punkcie P: (3 mnozenia)
float odleglosc_punktu_od_pl(Vector3 A, Vector3 N, Vector3 P)
{
  return fabs(N^(A-P));   // odleglosc punktu A od plaszczyzny
}

// Punkt przeciecia prostej wyznaczonej punktami A,B z plaszczyzna o normalnej N (o d³ugoœci 1) i punkcie P (7 mnozen)
// normal_vector N nie musi byc o dlugosci = 1.
Vector3 punkt_przec_prostej_z_plaszcz(Vector3 A, Vector3 B, Vector3 N, Vector3 P)
{
  float y = (B-A)^N;
  if (y != 0)
    return B + (B-A)*((P-B)^N)/y;
  else
    return B + (B-A)*1e10;              // punkt w nieskonczonosci  (wektor || do plaszczyzny)
}

// Punkt przeciecia dwoch prostych przy zalozeniu, ze obie proste
// leza na jednej plaszczyznie. Proste dane w postaci wektorow W (znormalizowane: d³ugoœæ = 1) i punktow P (19 mnozen)
Vector3 punkt_przec_dwoch_prostych(Vector3 W1, Vector3 P1, Vector3 W2, Vector3 P2)
{
  Vector3 N = W1*W2;             // normal_vector do plaszczyzny na ktorej leza obie proste
  Vector3 N2 = N*W1;             // normal_vector do plaszczyzny prostop. do N, na ktorej lezy prosta 1.
  return punkt_przec_prostej_z_plaszcz(P2, P2+W2, N2, P1);
}

// odleg³oœæ pomiêdzy prostymi wyznaczonymi przez punkty AB i CD + punkty le¿¹ce najbli¿ej na ka¿dej z prostych
float odleglosc_pom_prostymi(Vector3 A, Vector3 B, Vector3 C, Vector3 D, 
             Vector3 *Xab=NULL, Vector3 *Xcd=NULL)
{
  Vector3 N = ((B-A)*(D-C)); // normal_vector do p³aszczyzny na której le¿y jeden z odcinków np. AB i prostopad³ej do drugiego odcinka np. CD
  if (N.length() == 0) // proste równoleg³e
  {
    Vector3 Cpri = rzut_punktu_na_pl(C, (B-A).znorm(), A);  // rzut punktu C na p³aszczyznê zawieraj¹c¹ punkty prost. do prostych i przechodz¹c¹ przez A
    if ((Xab != NULL)&&(Xcd != NULL))            // jeœli chcemy jeszcze znaæ punkty le¿¹ce najbli¿ej siebie na poszczególnych prostych 
    {    
      *Xab = A;
      *Xcd = Cpri;
    }
    return (Cpri-A).length();
  }
  else
  {
    Vector3 Nznorm = N.znorm();    
    Vector3 Cprim = rzut_punktu_na_pl(C, Nznorm, A);  // rzut punktu C na p³aszczyznê zawieraj¹c¹ punkty A,B
    if ((Xab != NULL)&&(Xcd != NULL))            // jeœli chcemy jeszcze znaæ punkty le¿¹ce najbli¿ej siebie na poszczególnych prostych                                   
    {    
      Vector3 Dprim = rzut_punktu_na_pl(D, Nznorm, A);  // rzut punktu D na p³aszczyznê zawieraj¹c¹ punkty A,B
      *Xab = punkt_przec_dwoch_prostych((B-A).znorm(), A, (Dprim-Cprim).znorm(), Cprim);
      *Xcd = *Xab + C - Cprim;   
    }
    return (Cprim-C).length();
  }
}




// Sprawdzenie czy punkt lezacy na plaszczyznie ABC znajduje sie
// tez w trojkacie ABC:
bool czy_w_trojkacie(Vector3 A,Vector3 B, Vector3 C, Vector3 P)
{
  // 1.) Z kolejnych bokow wielokata wypuklego (jakim jest tez trojkat)
  //     tworze wektory zwrocone do kolejnych punktow np AB, BC, CA.
  //     Sprawdzam czy punkt P lezy zawsze z tej samej strony wektora -
  //     iloczyny wektorowe wektorow XY i XP powinny byc zawsze tak samo
  //     zwrocone (zwrot wyznaczam poprzez porownanie znakow z pierwsza lepsza
  //     niezerowa skladowa wektora normalnego do plaszczyzny ABC (18 mnozen w prz. trojkata)
  Vector3 AB = B-A, BC = C-B, CA = A-C, AP = P-A, BP = P-B, CP = P-C;
  Vector3 ilo1 = AB*AP, ilo2 = BC*BP, ilo3 = CA*CP;
  if (ilo1.x != 0)
  {
    int w = (ilo1.x > 0) + (ilo2.x > 0) + (ilo3.x > 0);
    if ((w == 0)||(w == 3)) return 1;
  }
  else if (ilo1.y != 0)
  {
    int w = (ilo1.y > 0) + (ilo2.y > 0) + (ilo3.y > 0);
    if ((w == 0)||(w == 3)) return 1;
  }
  else if (ilo1.z != 0)
  {
    int w = (ilo1.z > 0) + (ilo2.z > 0) + (ilo3.z > 0);
    if ((w == 0)||(w == 3)) return 1;
  }

  
  // 2.) Przeprowadzam prosta przez punkty A i P, wyznaczam punkt przeciecia X
  //     z prosta przeprowadzona przez B i C. Obliczam 6 odleglosci pomiedzy punktami
  //     (aby nie pierwiastkowac wystarcza iloczyny skalarne wektorow). Jesli |AP| + |PX| == |AX| oraz
  //     |BX| + |XC| == |BC| to punkt P lezy wewnatrz trojkata (18 mnozen + punkt przeciecia = 37 mnozen)


  return 0;
}






// zwraca kat pomiedzy wektorami w zakresie <0,2pi) w kierunku przeciwnym
// do ruchu wskazowek zegara. Zakladam, ze Wa.z = Wb.z = 0
float kat_pom_wekt2D(Vector3 Wa, Vector3 Wb)
{

  Vector3 ilo = Wa.znorm2D() * Wb.znorm2D();  // iloczyn wektorowy wektorow o jednostkowej dlugosci
  float sin_kata = ilo.z;        // problem w tym, ze sin(wheel_turn_angle) == sin(pi-wheel_turn_angle)   
  if (sin_kata == 0)
  {
    if (Wa.znorm2D() == Wb.znorm2D()) return 0; 
    if (Wa.znorm2D() == -Wb.znorm2D()) return pii;
  }
  // dlatego trzeba  jeszcze sprawdzic czy to kat rozwarty
  Vector3 wso_n = Wa.znorm2D() + Wb.znorm2D();          
  Vector3 ilo1 = wso_n.znorm2D() * Wb.znorm2D();
  bool kat_rozwarty = (ilo1.length() > sqrt(2.0)/2);
  
  float kat = asin(fabs(sin_kata));
  if (kat_rozwarty) kat = pii-kat;
  if (sin_kata < 0) kat = 2*pii - kat;

  return kat;
}      

/*
   wyznaczanie punktu przeciecia sie 2 odcinkow AB i CD lub ich przedluzen
   zwraca 1 jesli odcinki sie przecinaja 
*/
bool punkt_przeciecia2D(float *x,float *y,float xA,float yA, float xB, float yB,
                        float xC,float yC, float xD, float yD)
{
  float a1,b1,c1,a2,b2,c2;  // rownanie prostej: ax+by+c=0 
  a1 = (yB-yA); b1 = -(xB-xA); c1 = (xB-xA)*yA - (yB-yA)*xA;               
  a2 = (yD-yC); b2 = -(xD-xC); c2 = (xD-xC)*yC - (yD-yC)*xC;
  float mian = a1*b2-a2*b1;
  if (mian == 0) {*x=0;*y=0;return 0;}  // odcinki rownolegle
  float xx = (c2*b1 - c1*b2)/mian,
        yy = (c1*a2 - c2*a1)/mian;
  *x = xx; *y = yy;
  if (  (((xx > xA)&&(xx < xB))||((xx < xA)&&(xx > xB))||
         ((yy > yA)&&(yy < yB))||((yy < yA)&&(yy > yB))) &&
        (((xx > xC)&&(xx < xD))||((xx < xC)&&(xx > xD))||
         ((yy > yC)&&(yy < yD))||((yy < yC)&&(yy > yD)))
     )    
     return 1;
  else
     return 0;      
}

/*
    Minimalna odleglosc pomiedzy odcinkami AB i CD obliczana jako odleglosc 2 plaszczyzn
    wzajemnie rownoleglych , z ktorych kazda zawiera jeden z odcinkow (jesli rzuty odcinkow
    sie przecinaja) lub minimalna odleglosc ktoregos z punktow A,B,C lub D do drugiego odcinka 
    
    dodatkowo na wejsciu punkty na prostych AB i CD ktore mozna polaczyc 
    odcinkiem o minimalnej dlugosci oraz info czy rzuty odcinkow sie przecinaja
    (wowczas oba punkty Xab oraz Xcd leza na odcinkach AB i CD)


    // b³êdy! Trzeba to naprawiæ
*/
/*float odleglosc_pom_odcinkami(Vector3 A, Vector3 B, Vector3 C, Vector3 D, 
             Vector3 *Xab, Vector3 *Xcd, bool *czy_przeciecie)
{
  Vector3 AB = A-B, CD = C-D;
  Vector3 N = (AB*CD).znorm();             // wektor normalny do obu plaszczyzn rownoleglych
  
  if (N.length() == 0)  // odcinki rownolegle -> trzeba znalezc odleglosc pomiedzy prostymi
  {
      //Vector3 AC = A-C;
      //Vector3 W = AC*AB;
      Vector3 N2 = AB.znorm();             // normal_vector do plaszczyzny prostopadlej do odcinkow
      float d_N2_kw = N2^N2;
      float d = -A^N;                      // wspolczynnik d w rownaniu plaszczyzny ax+by+cz+d=0
                                           // przechodzacej przez punkt A 
                                           
      float kC = (C^N2 + d)/d_N2_kw;       // odleglosc pomiedzy C a C'
      Vector3 Cprim = C - N2*kC;           // rzut punktu C na plaszczyzne przechodzaca przez A                         
      float k = (A-Cprim).length();       // odleglosc pomiedzy prostymi
                               
      // trzeba jeszcze sprawdzic czy odcinki sa na tej samej wysokosci, jesli nie, to odlegloscia
      // pomiedzy odcinkami jest minimalna odleglosc pomiedzy parami punktow
      float kD = (D^N2 + d)/d_N2_kw,
            kB = (B^N2 + d)/d_N2_kw,
            kA = 0;
      
      if ( ((kA > kC)&&(kA > kD)&&(kB > kC)&&(kB > kD))||  // odcinki nie sa na tej samej wysokosci
           ((kA < kC)&&(kA < kD)&&(kB < kC)&&(kB < kD)) )
      {
           float d[] = {(A-C).length(), (A-D).length(), (B-C).length(), (B-D).length()};
           float d_min = 1e10;
           for (long i=0;i<4;i++) 
             if (d[i] < d_min) d_min = d[i];  
           k = d_min;  
      }     
      *Xab = A;
      *Xcd = Cprim; 
      *czy_przeciecie = 0;       
                                            
      return k;
  } // jesli odcinki rownolegle
  
  float d1 = -A^N, d2 = -C^N;  // wspolczynniki d w rownaniu plaszczyzny ax+by+cz+d=0
  float k = (d1-d2)/(N^N);     // |k| - odleglosc plaszczyzn -> minimalna odleglosc pomiedzy prostymi
  Vector3 Ap = N*k + A, Bp = N*k + B; // rzuty punktow A i B na plaszczyzne prostej CD
  float xx,yy;                        // wspolrzedne punktu przeciecia X na plaszczyznie rzutowania
  float propAX_AB,propCX_CD;          // proporcje |AX|/|AB| i |CX|/|CD| 
  
  // rzutuje wszystkie punkty na jedna z 3 plaszczyzn globalnego ukl. wspolrzednych
  // tak, aby zaden z odcinkow nie zamienil sie w punkt (wtedy, gdy obie skladowe rzutu wektora ==0)
  if (  ( ((AB.x == 0)&&(AB.y == 0))||((CD.x == 0)&&(CD.y == 0)) )||
        ( ((AB.x == 0)&&(AB.z == 0))||((CD.x == 0)&&(CD.z == 0)) )  ) // rzutowanie na x==0 
  {
       *czy_przeciecie = punkt_przeciecia2D(&xx,&yy,Ap.y,Ap.z,Bp.y,Bp.z,C.y,C.z,D.y,D.z);

       (*Xcd).y = xx;
       (*Xcd).z = yy;
       if (CD.y != 0)     
           propCX_CD = ((*Xcd).y - C.y)/CD.y;         
       else
           propCX_CD = ((*Xcd).z - C.z)/CD.z;  
       (*Xcd).x = C.x + propCX_CD*CD.x;
        
       (*Xab).y = xx;
       (*Xab).z = yy;
       if (AB.y != 0)     
           propAX_AB = ((*Xab).y - Ap.y)/AB.y;
       else
           propAX_AB = ((*Xab).z - Ap.z)/AB.z;
       (*Xab).x = Ap.x + propAX_AB*AB.x;  
       *Xab = *Xab - N*k;    // rzutowania powrotne na plaszczyzne odcinka AB
  }
  else  // rzutowanie na z==0 (choc moglo by byc rowniez na y==0) 
  {
       *czy_przeciecie = punkt_przeciecia2D(&xx,&yy,Ap.x,Ap.y,Bp.x,Bp.y,C.x,C.y,D.x,D.y);

       (*Xcd).x = xx;
       (*Xcd).y = yy;
       if (CD.y != 0)     
           propCX_CD = ((*Xcd).y - C.y)/CD.y;         
       else
           propCX_CD = ((*Xcd).x - C.x)/CD.x;  
       (*Xcd).z = C.z + propCX_CD*CD.z;
        
       (*Xab).x = xx;
       (*Xab).y = yy;
       if (AB.y != 0)     
           propAX_AB = ((*Xab).y - Ap.y)/AB.y;
       else
           propAX_AB = ((*Xab).x - Ap.x)/AB.x;
       (*Xab).z = Ap.z + propAX_AB*AB.z;  
       *Xab = *Xab - N*k;    // rzutowania powrotne na plaszczyzne odcinka AB
  }
  
  float min_dist = fabs(k);
  
  if (*czy_przeciecie == 0)  // jesli rzuty sie nie przecinaja, to musze sprawdzic, czy 
  {         // jeden z rz. odcinkow przecina sie z prosta, na ktorej lezy drugi
       min_dist = 1e10;
       if ((fabs(propAX_AB) > 1)&& (fabs(propCX_CD) > 1))  // jesli nie, to biore minimalna
       {                                // odleglosc pomiedzy koncami odcinkow
           float d[] = {(A-C).length(), (A-D).length(), (B-C).length(), (B-D).length()};
           for (long i=0;i<4;i++) 
             if (d[i] < min_dist) min_dist = d[i];                        
       }    
       else                           
         if (fabs(propAX_AB) > 1)    // punkt X poza odcinkiem AB
         {
           float d[] = {(A-*Xcd).length(), (B-*Xcd).length()};
           for (long i=0;i<2;i++) 
             if (d[i] < min_dist) min_dist = d[i];                        
         }
         else                        // punkt X musi byc poza odc. CD
         {
           float d[] = {(C-*Xab).length(), (D-*Xab).length()};
           for (long i=0;i<2;i++) 
             if (d[i] < min_dist) min_dist = d[i];      
         }
  }   
  
  //return min_dist;  
  return (*Xab - *Xcd).length();
}
*/


void wektory_sprawdzenie_dodatkow()
{
  FILE *f = fopen("wektor_plik.txt","w");
  Vector3 A(3,4,0), B(0,0,0), C(5,0,0), P1(2,1,10),P2(2,1,12);
  Vector3 N = normal_vector(A,B,C);
  Vector3 P = punkt_przec_prostej_z_plaszcz(P1,P2,N,A);
  Vector3 P_prost = rzut_punktu_na_pl(P1,N,A);
  float odl = odleglosc_punktu_od_pl(P1,N,A);
  fprintf(f,"normal_vector do pl. ABC: N = (%f, %f, %f)\n",N.x,N.y,N.z);
  fprintf(f,"punkt na plaszczyznie P = (%f, %f, %f) po zrzut. punktu P1 w kier. wektora P2P1\n",P.x,P.y,P.z);
  fprintf(f,"rzut prostopadly punktu P1: P_prost = (%f, %f, %f)\n",P_prost.x,P_prost.y,P_prost.z);
  Vector3 Pp  = rzut_punktu_na_prosta(A,B,C);
  fprintf(f,"rzut punktu A na prosta BC = (%f,%f,%f)\n",Pp.x,Pp.y,Pp.z);
  fprintf(f,"odleglosc P1 od plaszczyzny ABC = %f\n",odl);
  Vector3 X(4,0.1,0);
  fprintf(f,"czy punkt X w trojkacie = %d\n", czy_w_trojkacie(A,B,C,X));
  Vector3 Y = punkt_przec_dwoch_prostych(B-A,A,P-C,C);
  fprintf(f,"punkt przeciecia sie prostych AB i PC: Y = (%f, %f, %f)\n",Y.x,Y.y,Y.z);

  // sprawdzenie w jaki sposob zmienia sie odleglosc punktu od plaszczyzny opisanej trzema punktami,
  // gdy wszystkie 4 punkty sa w ruchu:
  Vector3 Va(1,2,-1), Vb(2,0.5,1), Vc(0,0,-2), Vp1(-1,-1,0);
  float dt = 0.01;                      // przedzial czasu, co jaki modyfikowane jest position punktow
  float odl_pop = 0;
  for (long i=0;i<1000;i++)
  {
    A = A+Va*dt; B = B+Vb*dt; C = C+Vc*dt; P1 = P1+Vp1*dt;
    N = normal_vector(A,B,C);
    float zmiana = odl-odl_pop;
    odl_pop = odl;
    odl = odleglosc_punktu_od_pl(P1,N,A);
    fprintf(f,"odleglosc = %f, zmiana = %f, zm. zmiany = %f\n",odl,odl-odl_pop, odl-odl_pop - zmiana);
  }

  Vector3 AA(2,7,2), BB(2,-10,2), CC(5,5,4), DD(5,7,4);       // odcinki równoleg³e 
  //Vector3 AA(2,7,2), BB(2,-10,2), CC(0,5,6), DD(1,5,5);     // odcinki prostopad³e do siebie  
  //Vector3 AA(2,3,4), BB(4,1,7), CC(0,2,6), DD(1,7,5);     // punkty najbli¿sze wewn¹trz odcinków AB i CD
  //Vector3 AA(2,3,4), BB(4,1,7), CC(10,12,16), DD(11,17,15);     // punkty najbli¿sze na zewn¹trz odcinków AB i CD
  Vector3 Xab1,Xcd1,Xab2,Xcd2;
  bool b;
  float odl1 = odleglosc_pom_prostymi(AA, BB, CC, DD, &Xab1,&Xcd1);
  float odl2 = 0;//odleglosc_pom_odcinkami(AA, BB, CC, DD, &Xab2,&Xcd2,&b);     

  fprintf(f,"porownanie funkcji odleglosc_pom_prostymi i odleglosc_pom_odcinkami:\n");
  fprintf(f,"odl1 = %f, odl2 = %f, Xab1 = (%f,%f,%f), Xab2 = (%f,%f,%f)\n",odl1,odl2, Xab1.x,Xab1.y,Xab1.z,Xab2.x,Xab2.y,Xab2.z);
  fprintf(f,"Xcd1 = (%f,%f,%f), Xcd2 = (%f,%f,%f)\n",Xcd1.x,Xcd1.y,Xcd1.z,Xcd2.x,Xcd2.y,Xcd2.z);


  // odleg³oœæ pomiêdzy punktem a odcinkiem:
  fprintf(f, "\nTestowanie odleglosci pomiedzy punktem a odcinkiem:\n\n");
  A = Vector3(0, 0, 0); B = Vector3(4, 0, 0);
  for (float tx = -1; tx <= 6; tx += 0.5)
	  for (float tz = -1; tz <= 1; tz += 0.5)
	  {
		  Vector3 P = Vector3(tx, 0, tz);
		  Vector3 PN = najblizszy_punkt_na_odcinku(P, A, B);
		  //Vector3 R = rzut_punktu_na_prosta(P, A, B);
		  float odl = odleglosc_pom_punktem_a_odcinkiem(P, A, B);
		  fprintf(f, "  tx = %f, tz = %f, odleglosc = %f, PN = (%f, %f, %f)\n", tx, tz, odl, PN.x, PN.y, PN.z);
	  }

  fclose(f);
}

