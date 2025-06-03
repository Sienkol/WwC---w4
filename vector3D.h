

#define _VECTOR3D_H
//#define float double

class Vector3
{
public:      
  float x,y,z;
  Vector3();
  Vector3(float _x,float _y, float _z);
  Vector3 operator* (float value);
  
  Vector3 operator/ (float value);
  Vector3 operator+=(Vector3 v);    // dodanie vec+vec
  Vector3 operator+(Vector3 v);     // dodanie vec+vec
  Vector3 operator+=(float constant);    // dodanie vec+liczba
  Vector3 operator+(float constant);     // dodanie vec+liczba
  Vector3 operator-=(Vector3 v);    // dodanie vec+vec
  Vector3 operator-(Vector3 v);     // odejmowanie vec-vec
  Vector3 operator*(Vector3 v);     // iloczyn wektorowy
  Vector3 operator- ();              // odejmowanie vec-vec
  bool operator==(Vector3 v2); // porownanie
  Vector3 obrot(float wheel_turn_angle,float vn0,float vn1,float vn2);
  Vector3 obrot(float wheel_turn_angle,Vector3 os);
  Vector3 znorm();
  Vector3 znorm2D();
  float operator^(Vector3 v);        // iloczyn scalarny
  float length(); // length aktualnego wektora    
};

Vector3 normal_vector(Vector3 A,Vector3 B, Vector3 C);  // normal_vector do trojkata ABC

// rzut punktu A na plaszczyzne o normalnej N i punkcie P:
Vector3 rzut_punktu_na_pl(Vector3 A, Vector3 N, Vector3 P);

// rzut prostopadly punktu P na prosta AB
Vector3 rzut_punktu_na_prosta(Vector3 P, Vector3 A, Vector3 B);

// najbli¿szy punkt le¿¹cy na odcinku AB do punktu P:
Vector3 najblizszy_punkt_na_odcinku(Vector3 P, Vector3 A, Vector3 B);

// odleglosc punktu A od plaszczyzny o normalnej N i punkcie P:
float odleglosc_punktu_od_pl(Vector3 A, Vector3 N, Vector3 P);

// odleglosc pomiêdzy punktem P a prost¹ wyznaczana przez punkty A,B
float odleglosc_pom_punktem_a_prosta(Vector3 P, Vector3 A, Vector3 B);

// ró¿ni siê od poprzedniej funkcji tym, ¿e jest ograniczona do odcinka, czyli jeœli
// rzut punktu le¿y poza odcinkiem to wynikiem jest odleg³oœæ do najbli¿szego punktu ze zb. {A,B}
float odleglosc_pom_punktem_a_odcinkiem(Vector3 P, Vector3 A, Vector3 B);

// Punkt przeciecia wektora AB z plaszczyzna o normalnej N i punkcie P
Vector3 punkt_przec_prostej_z_plaszcz(Vector3 A, Vector3 B, Vector3 N, Vector3 P);

// Punkt przeciecia dwoch prostych przy zalozeniu, ze obie proste
// leza na jednej plaszczyznie. Proste dane w postaci wektorow W i punktow P (19 mnozen)
Vector3 punkt_przec_dwoch_prostych(Vector3 W1, Vector3 P1, Vector3 W2, Vector3 P2);

// odleg³oœæ pomiêdzy prostymi wyznaczonymi przez punkty AB i CD + punkty le¿¹ce najbli¿ej na ka¿dej z prostych
float odleglosc_pom_prostymi(Vector3 A, Vector3 B, Vector3 C, Vector3 D, 
             Vector3 *Xab, Vector3 *Xcd);

// Sprawdzenie czy punkt lezacy na plaszczyznie ABC znajduje sie
// tez w trojkacie ABC:
bool czy_w_trojkacie(Vector3 A,Vector3 B, Vector3 C, Vector3 P);

float kat_pom_wekt2D(Vector3 Wa, Vector3 Wb);  // zwraca kat pomiedzy wektorami

/*
   wyznaczanie punktu przeciecia sie 2 odcinkow AB i CD lub ich przedluzen
   zwraca 1 jesli odcinki sie przecinaja 
*/
bool punkt_przeciecia2D(float *x,float *y,float xA,float yA, float xB, float yB,
                        float xC,float yC, float xD, float yD);

/*
    Minimalna odleglosc pomiedzy odcinkami AB i CD obliczana jako odleglosc 2 plaszczyzn
    wzajemnie rownoleglych , z ktorych kazda zawiera jeden z odcinkow (jesli rzuty odcinkow
    sie przecinaja) lub minimalna odleglosc ktoregos z punktow A,B,C lub D do drugiego odcinka 
    
    dodatkowo na wejsciu punkty na prostych AB i CD ktore mozna polaczyc 
    odcinkiem o minimalnej dlugosci oraz info czy rzuty odcinkow sie przecinaja
    (wowczas oba punkty Xab oraz Xcd leza na odcinkach AB i CD)
*/
//float odleglosc_pom_odcinkami(Vector3 A, Vector3 B, Vector3 C, Vector3 D, 
//             Vector3 *Xab, Vector3 *Xcd, bool *czy_przeciecie);



void wektory_sprawdzenie_dodatkow();


