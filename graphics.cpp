/************************************************************
Grafika OpenGL
*************************************************************/
#include <windows.h>
#include <gl\gl.h>
#include <gl\glu.h>
#include <iterator> 
#include <map>
#include <time.h>

#include "graphics.h"
//#include "vector3D.h"
//#include "quaternion.h"
#ifndef _OBJECTS__H
#include "objects.h"
#endif
using namespace std;


extern FILE *f;
extern MovableObject *my_vehicle;               // obiekt przypisany do tej aplikacji 
extern map<int, MovableObject*> network_vehicles;
extern CRITICAL_SECTION m_cs;
extern Terrain terrain;

extern long group_existing_time;
extern long start_time;

int g_GLPixelIndex = 0;
HGLRC g_hGLContext = NULL;
unsigned int font_base;

ViewParameters par_view;

extern void TworzListyWyswietlania();		// definiujemy listy tworzące labirynt
extern void DrawGlobalCoordinateSystem();

void StandardViewParametersSetting(ViewParameters *p)
{
	p->initial_camera_direction = Vector3(0, -3, -11);   // direction patrzenia
	p->initial_camera_position = Vector3(30, 3, 0);          // po³o¿enie kamery
	p->initial_camera_vertical = Vector3(0, 1, 0);           // direction pionu kamery             

	// Zmienne - ustawiane przez użytkownika
	p->tracking = 1;                             // tryb œledzenia obiektu przez kamerê
	p->top_view = 0;                          // tryb widoku z gory
	p->distance = 20.0;                          // distance lub przybli¿enie kamery
	p->zoom = 1.1;                               // zmiana kąta widzenia
	p->cam_angle_z = 0;                            // obrót kamery góra-dół

	p->shift_to_right = 0;                        // przesunięcie kamery w prawo (w lewo o wart. ujemnej) - chodzi głównie o tryb edycji
	p->shift_to_bottom = 0;                          // przesunięcie do dołu (w górę o wart. ujemnej)          i widok z góry (klawisz Q)  
}

int GraphicsInitialization(HDC g_context)
{

	if (SetWindowPixelFormat(g_context) == FALSE)
		return FALSE;

	if (CreateViewGLContext(g_context) == FALSE)
		return 0;
	BuildFont(g_context);

	glEnable(GL_DEPTH_TEST);
	glDepthFunc(GL_LEQUAL);

	StandardViewParametersSetting(&par_view);

	TworzListyWyswietlania();		// definiujemy listy tworzące różne elementy sceny
	terrain.GraphicsInitialization();
}

// Ustwienia kamery w zależności od wartości początkowych (w interakcji), wartości ustawianych
// przez użytkowika oraz stanu obiektu (np. gdy tryb śledzenia)
void CameraSettings(Vector3 *position, Vector3 *direction, Vector3 *vertical, ViewParameters pw)
{
	if (pw.tracking)  // kamera ruchoma - porusza się wraz z obiektem
	{
		(*direction) = my_vehicle->state.qOrient.obroc_wektor(Vector3(1, 0, 0));
		(*vertical) = my_vehicle->state.qOrient.obroc_wektor(Vector3(0, 1, 0));
		Vector3 prawo_kamery = my_vehicle->state.qOrient.obroc_wektor(Vector3(0, 0, 1));

		(*vertical) = (*vertical).obrot(pw.cam_angle_z, prawo_kamery.x, prawo_kamery.y, prawo_kamery.z);
		(*direction) = (*direction).obrot(pw.cam_angle_z, prawo_kamery.x, prawo_kamery.y, prawo_kamery.z);
		(*position) = my_vehicle->state.vPos - (*direction)*my_vehicle->length * 0 +
			(*vertical).znorm()*my_vehicle->height * 5;
		if (pw.top_view)
		{
			(*vertical) = (*direction);
			(*direction) = Vector3(0, -1, 0);
			(*position) = (*position) + Vector3(0, 100, 0) + (*vertical)*pw.shift_to_bottom + (*vertical)*(*direction)*pw.shift_to_right;
		}
	}
	else // bez śledzenia - kamera nie podąża wraz z pojazdem
	{
		(*vertical) = pw.initial_camera_vertical;
		(*direction) = pw.initial_camera_direction;
		(*position) = pw.initial_camera_position;
		Vector3 prawo_kamery = ((*direction)*(*vertical)).znorm();
		(*vertical) = (*vertical).obrot(pw.cam_angle_z / 20, prawo_kamery.x, prawo_kamery.y, prawo_kamery.z);
		(*direction) = (*direction).obrot(pw.cam_angle_z / 20, prawo_kamery.x, prawo_kamery.y, prawo_kamery.z);
		if (pw.top_view)
		{
			(*vertical) = Vector3(0, 0, -1);
			(*direction) = Vector3(0, -1, 0.02);
			(*position) = pw.initial_camera_position + Vector3(0, 100, 0) + (*vertical)*pw.shift_to_bottom + (*vertical)*(*direction)*pw.shift_to_right;
		}
	}
}


void DrawScene()
{
	float czas = (float)(group_existing_time + clock() - start_time) / CLOCKS_PER_SEC;  // czas od uruchomienia w [s]
	GLfloat OwnObjectColor[] = { 0.0f, 0.0f, 0.9f, 0.7f };
	GLfloat BlueSurfaceTr[] = { 0.6f, 0.0f, 0.9f, 0.3f };

	GLfloat NetworkVehiclesColor[] = { 0.2f, 0.5f, 0.4f, 0.5f };
	GLfloat RedSurface[] = { 0.6f, 0.2f, 0.1f, 0.5f };
	GLfloat OrangeSurface[] = { 1.0f, 0.8f, 0.0f, 0.7f };
	GLfloat GreenSurface[] = { 0.15f, 0.62f, 0.3f, 1.0f };
	GLfloat YellowSurface[] = { 0.75f, 0.75f, 0.0f, 1.0f };
	GLfloat YellowLight[] = { 2.0f, 2.0f, 1.0f, 1.0f };

	GLfloat LightAmbient[] = { 0.1f, 0.1f, 0.1f, 0.1f };
	GLfloat LightDiffuse[] = { 0.7f, 0.7f, 0.7f, 0.7f };

	GLfloat LightPosition[] = { 10.0*cos(czas / 5), 5.0f, 10.0*sin(czas / 5), 0.0f };


	glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

	glLightfv(GL_LIGHT0, GL_AMBIENT, LightAmbient);		//1 składowa: światło otaczające (bezkierunkowe)
	glLightfv(GL_LIGHT0, GL_DIFFUSE, LightDiffuse);		//2 składowa: światło rozproszone (kierunkowe)
	glLightfv(GL_LIGHT0, GL_POSITION, LightPosition);
	glEnable(GL_LIGHT0);

	//glPushMatrix();
	glMaterialfv(GL_FRONT_AND_BACK, GL_AMBIENT_AND_DIFFUSE, YellowLight);


	glLoadIdentity();
	glClearColor(0.1, 0.1, 0.4, 0.7);   // ustawienie nieczarnego koloru tła
	glTranslatef(-24, 24, -40);
	glRasterPos2f(4.0, -4.0);
	glPrint("%s", par_view.inscription1);
	glPrint("%s", par_view.inscription2);
	glLoadIdentity();


	Vector3 pol_k, kierunek_k, pion_k;

	CameraSettings(&pol_k, &kierunek_k, &pion_k, par_view);

	gluLookAt(pol_k.x - par_view.distance*kierunek_k.x,
		pol_k.y - par_view.distance*kierunek_k.y, pol_k.z - par_view.distance*kierunek_k.z,
		pol_k.x + kierunek_k.x, pol_k.y + kierunek_k.y, pol_k.z + kierunek_k.z,
		pion_k.x, pion_k.y, pion_k.z);

	//glRasterPos2f(0.30,-0.27);
	//glPrint("MojObiekt->iID = %d",my_vehicle->iID ); 

	DrawGlobalCoordinateSystem();

	int dw = 0, dk = 0;
	if (terrain.if_toroidal_world)
	{
		if (terrain.border_x > 0) dk = 1;
		if (terrain.border_z > 0) dw = 1;
	}

	for (int w = -dw; w < 1 + dw; w++)
		for (int k = -dk; k < 1 + dk; k++)
		{
			glPushMatrix();

			glTranslatef(terrain.border_x*k, 0, terrain.border_z*w);

			glMaterialfv(GL_FRONT_AND_BACK, GL_AMBIENT_AND_DIFFUSE, OwnObjectColor);
			glEnable(GL_BLEND);

			my_vehicle->DrawObject();

			// Lock the Critical section
			EnterCriticalSection(&m_cs);
			for (map<int, MovableObject*>::iterator it = network_vehicles.begin(); it != network_vehicles.end(); ++it)
			{
				if (it->second)
				{
					glMaterialfv(GL_FRONT_AND_BACK, GL_AMBIENT_AND_DIFFUSE, NetworkVehiclesColor);
					it->second->DrawObject();
				}
			}
			//Release the Critical section
			LeaveCriticalSection(&m_cs);
			
			glDisable(GL_BLEND);
			glMaterialfv(GL_FRONT_AND_BACK, GL_AMBIENT_AND_DIFFUSE, GreenSurface);
			
			terrain.DrawObject();
			glPopMatrix();
		}

	//glPopMatrix();	
	glFlush();
}




void WindowSizeChange(int cx, int cy)
{
	GLsizei width, height;
	GLdouble aspect;
	width = cx;
	height = cy;

	if (cy == 0)
		aspect = (GLdouble)width;
	else
		aspect = (GLdouble)width / (GLdouble)height;

	glViewport(0, 0, width, height);


	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	gluPerspective(55 * par_view.zoom, aspect, 1, 1000000.0);

	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();

	glDrawBuffer(GL_BACK);

	glEnable(GL_LIGHTING);

	glEnable(GL_DEPTH_TEST);

}

Vector3 Cursor3dCoordinates(int x, int y) // współrzędne 3D punktu na obrazie 2D
{
	//  pobranie macierz modelowania
	GLdouble model[16];
	glGetDoublev(GL_MODELVIEW_MATRIX, model);

	// pobranie macierzy rzutowania
	GLdouble proj[16];
	glGetDoublev(GL_PROJECTION_MATRIX, proj);

	// pobranie obszaru renderingu
	GLint view[4];
	glGetIntegerv(GL_VIEWPORT, view);

	// tablice ze odczytanymi współrzędnymi w przestrzeni widoku
	GLdouble wsp[3];

	//RECT rc;
	//GetClientRect (main_window, &rc);

	GLdouble wsp_z;

	int wynik = gluProject(0, 0, 0, model, proj, view, wsp + 0, wsp + 1, &wsp_z);

	gluUnProject(x, y, wsp_z, model, proj, view, wsp + 0, wsp + 1, wsp + 2);
	//gluUnProject (x,rc.bottom - y,wsp_z ,model,proj,view,wsp+0,wsp+1,wsp+2);
	return Vector3(wsp[0], wsp[1], wsp[2]);
}

Vector3 Cursor3dCoordinates(int x, int y, float height) // współrzędne 3D punktu na obrazie 2D
{
	glTranslatef(0, height, 0);
	//  pobranie macierz modelowania
	GLdouble model[16];
	glGetDoublev(GL_MODELVIEW_MATRIX, model);

	// pobranie macierzy rzutowania
	GLdouble proj[16];
	glGetDoublev(GL_PROJECTION_MATRIX, proj);

	// pobranie obszaru renderingu
	GLint view[4];
	glGetIntegerv(GL_VIEWPORT, view);

	// tablice ze odczytanymi współrzędnymi w przestrzeni widoku
	GLdouble wsp[3];

	//RECT rc;
	//GetClientRect (main_window, &rc);

	GLdouble wsp_z;

	int wynik = gluProject(0, 0, 0, model, proj, view, wsp + 0, wsp + 1, &wsp_z);
	gluUnProject(x, y, wsp_z, model, proj, view, wsp + 0, wsp + 1, wsp + 2);
	glTranslatef(0, -height, 0);
	//gluUnProject (x,rc.bottom - y,wsp_z ,model,proj,view,wsp+0,wsp+1,wsp+2);
	return Vector3(wsp[0], wsp[1], wsp[2]);
}

void ScreenCoordinates(float *xx, float *yy, float *zz, Vector3 Point3D) // współrzędne punktu na ekranie na podstawie wsp 3D
{
	//  pobranie macierz modelowania
	GLdouble model[16];
	glGetDoublev(GL_MODELVIEW_MATRIX, model);
	// pobranie macierzy rzutowania
	GLdouble proj[16];
	glGetDoublev(GL_PROJECTION_MATRIX, proj);
	// pobranie obszaru renderingu
	GLint view[4];
	glGetIntegerv(GL_VIEWPORT, view);
	// tablice ze odczytanymi współrzędnymi w przestrzeni widoku
	GLdouble wsp[3], wsp_okn[3];
	GLdouble liczba;
	int wynik = gluProject(Point3D.x, Point3D.y, Point3D.z, model, proj, view, wsp_okn + 0, wsp_okn + 1, wsp_okn + 2);
	gluUnProject(wsp_okn[0], wsp_okn[1], wsp_okn[2], model, proj, view, wsp + 0, wsp + 1, wsp + 2);
	//fprintf(f,"   Wsp. punktu 3D = (%f, %f, %f), wspolrzedne w oknie = (%f, %f, %f), wsp. punktu = (%f, %f, %f)\n",
	//  Point3D.x,Point3D.y,Point3D.z,  wsp_okn[0],wsp_okn[1],wsp_okn[2],  wsp[0],wsp[1],wsp[2]);

	(*xx) = wsp_okn[0]; (*yy) = wsp_okn[1]; (*zz) = wsp_okn[2];
}

void EndOfGraphics()
{
	if (wglGetCurrentContext() != NULL)
	{
		// dezaktualizacja kontekstu renderującego
		wglMakeCurrent(NULL, NULL);
	}
	if (g_hGLContext != NULL)
	{
		wglDeleteContext(g_hGLContext);
		g_hGLContext = NULL;
	}
	glDeleteLists(font_base, 96);
}

BOOL SetWindowPixelFormat(HDC hDC)
{
	PIXELFORMATDESCRIPTOR pixelDesc;

	pixelDesc.nSize = sizeof(PIXELFORMATDESCRIPTOR);
	pixelDesc.nVersion = 1;
	pixelDesc.dwFlags = PFD_DRAW_TO_WINDOW | PFD_SUPPORT_OPENGL | PFD_DOUBLEBUFFER | PFD_STEREO_DONTCARE;
	pixelDesc.iPixelType = PFD_TYPE_RGBA;
	pixelDesc.cColorBits = 32;
	pixelDesc.cRedBits = 8;
	pixelDesc.cRedShift = 16;
	pixelDesc.cGreenBits = 8;
	pixelDesc.cGreenShift = 8;
	pixelDesc.cBlueBits = 8;
	pixelDesc.cBlueShift = 0;
	pixelDesc.cAlphaBits = 0;
	pixelDesc.cAlphaShift = 0;
	pixelDesc.cAccumBits = 64;
	pixelDesc.cAccumRedBits = 16;
	pixelDesc.cAccumGreenBits = 16;
	pixelDesc.cAccumBlueBits = 16;
	pixelDesc.cAccumAlphaBits = 0;
	pixelDesc.cDepthBits = 32;
	pixelDesc.cStencilBits = 8;
	pixelDesc.cAuxBuffers = 0;
	pixelDesc.iLayerType = PFD_MAIN_PLANE;
	pixelDesc.bReserved = 0;
	pixelDesc.dwLayerMask = 0;
	pixelDesc.dwVisibleMask = 0;
	pixelDesc.dwDamageMask = 0;
	g_GLPixelIndex = ChoosePixelFormat(hDC, &pixelDesc);

	if (g_GLPixelIndex == 0)
	{
		g_GLPixelIndex = 1;

		if (DescribePixelFormat(hDC, g_GLPixelIndex, sizeof(PIXELFORMATDESCRIPTOR), &pixelDesc) == 0)
		{
			return FALSE;
		}
	}

	if (SetPixelFormat(hDC, g_GLPixelIndex, &pixelDesc) == FALSE)
	{
		return FALSE;
	}

	return TRUE;
}
BOOL CreateViewGLContext(HDC hDC)
{
	g_hGLContext = wglCreateContext(hDC);

	if (g_hGLContext == NULL)
	{
		return FALSE;
	}

	if (wglMakeCurrent(hDC, g_hGLContext) == FALSE)
	{
		return FALSE;
	}

	return TRUE;
}

GLvoid BuildFont(HDC hDC)								// Build Our Bitmap Font
{
	HFONT	font;										// Windows Font ID
	HFONT	oldfont;									// Used For Good House Keeping

	font_base = glGenLists(96);								// Storage For 96 Characters

	font = CreateFont(-13,							// Height Of Font
		0,								// Width Of Font
		0,								// Angle Of Escapement
		0,								// Orientation Angle
		FW_NORMAL,						// Font Weight
		TRUE,							// Italic
		FALSE,							// Underline
		FALSE,							// Strikeout
		ANSI_CHARSET,					// Character Set Identifier
		OUT_TT_PRECIS,					// Output Precision
		CLIP_DEFAULT_PRECIS,			// Clipping Precision
		ANTIALIASED_QUALITY,			// Output Quality
		FF_DONTCARE | DEFAULT_PITCH,		// Family And Pitch
		"Courier New");					// Font Name

	oldfont = (HFONT)SelectObject(hDC, font);           // Selects The Font We Want
	wglUseFontBitmaps(hDC, 31, 96, font_base);				// Builds 96 Characters Starting At Character 32
	SelectObject(hDC, oldfont);							// Selects The Font We Want
	DeleteObject(font);									// Delete The Font
}

// Napisy w OpenGL
GLvoid glPrint(const char *fmt, ...)	// Custom GL "Print" Routine
{
	char		text[256];	// Holds Our String
	va_list		ap;		// Pointer To List Of Arguments

	if (fmt == NULL)		// If There's No Text
		return;			// Do Nothing

	va_start(ap, fmt);		// Parses The String For Variables
	vsprintf(text, fmt, ap);	// And Converts Symbols To Actual Numbers
	va_end(ap);			// Results Are Stored In Text

	glPushAttrib(GL_LIST_BIT);	// Pushes The Display List Bits
	glListBase(font_base - 31);		// Sets The Base Character to 32
	glCallLists(strlen(text), GL_UNSIGNED_BYTE, text);	// Draws The Display List Text
	glPopAttrib();			// Pops The Display List Bits
}


void TworzListyWyswietlania()
{
	glNewList(Wall1, GL_COMPILE);	// GL_COMPILE - lista jest kompilowana, ale nie wykonywana

	glBegin(GL_QUADS);		// inne opcje: GL_POINTS, GL_LINES, GL_LINE_STRIP, GL_LINE_LOOP
	// GL_TRIANGLES, GL_TRIANGLE_STRIP, GL_TRIANGLE_FAN, GL_QUAD_STRIP, GL_POLYGON
	glNormal3f(-1.0, 0.0, 0.0);
	glVertex3f(-1.0, -1.0, 1.0);
	glVertex3f(-1.0, 1.0, 1.0);
	glVertex3f(-1.0, 1.0, -1.0);
	glVertex3f(-1.0, -1.0, -1.0);
	glEnd();
	glEndList();

	glNewList(Wall2, GL_COMPILE);
	glBegin(GL_QUADS);
	glNormal3f(1.0, 0.0, 0.0);
	glVertex3f(1.0, -1.0, 1.0);
	glVertex3f(1.0, 1.0, 1.0);
	glVertex3f(1.0, 1.0, -1.0);
	glVertex3f(1.0, -1.0, -1.0);
	glEnd();
	glEndList();

	/*glNewList(Floor,GL_COMPILE);
	glBegin(GL_POLYGON);
	glNormal3f( 0.0, 1.0, 0.0);
	glVertex3f( -100, 0, -300.0);
	glVertex3f( -100, 0, 100.0);
	glVertex3f( 100, 0, 100.0);
	glVertex3f( 100, 0, -300.0);
	glEnd();
	glEndList();*/

	glNewList(Cube, GL_COMPILE);
	glBegin(GL_QUADS);
	// przod
	glNormal3f(0.0, 0.0, 1.0);
	glVertex3f(0, 0, 1);
	glVertex3f(0, 1, 1);
	glVertex3f(1, 1, 1);
	glVertex3f(1, 0, 1);
	// tyl
	glNormal3f(0.0, 0.0, -1.0);
	glVertex3f(0, 0, 0);
	glVertex3f(1, 0, 0);
	glVertex3f(1, 1, 0);
	glVertex3f(0, 1, 0);
	// gora
	glNormal3f(0.0, 1.0, 0.0);
	glVertex3f(0, 1, 0);
	glVertex3f(0, 1, 1);
	glVertex3f(1, 1, 1);
	glVertex3f(1, 1, 0);
	// dol
	glNormal3f(0.0, -1.0, 0.0);
	glVertex3f(0, 0, 0);
	glVertex3f(1, 0, 0);
	glVertex3f(1, 0, 1);
	glVertex3f(0, 0, 1);
	// prawo
	glNormal3f(1.0, 0.0, 0.0);
	glVertex3f(1, 0, 0);
	glVertex3f(1, 0, 1);
	glVertex3f(1, 1, 1);
	glVertex3f(1, 1, 0);
	// lewo
	glNormal3f(-1.0, 0.0, 0.0);
	glVertex3f(0, 0, 0);
	glVertex3f(0, 1, 0);
	glVertex3f(0, 1, 1);
	glVertex3f(0, 0, 1);

	glEnd();
	glEndList();

	glNewList(Cube_skel, GL_COMPILE);
	glBegin(GL_LINES);
	glVertex3f(0, 0, 0);
	glVertex3f(1, 0, 0);
	glVertex3f(0, 1, 0);
	glVertex3f(1, 1, 0);
	glVertex3f(0, 0, 1);
	glVertex3f(1, 0, 1);
	glVertex3f(0, 1, 1);
	glVertex3f(1, 1, 1);
	glVertex3f(0, 0, 0);
	glVertex3f(0, 1, 0);
	glVertex3f(1, 0, 0);
	glVertex3f(1, 1, 0);
	glVertex3f(0, 0, 1);
	glVertex3f(0, 1, 1);
	glVertex3f(1, 0, 1);
	glVertex3f(1, 1, 1);
	glVertex3f(0, 0, 0);
	glVertex3f(0, 0, 1);
	glVertex3f(1, 0, 0);
	glVertex3f(1, 0, 1);
	glVertex3f(0, 1, 0);
	glVertex3f(0, 1, 1);
	glVertex3f(1, 1, 0);
	glVertex3f(1, 1, 1);
	glVertex3f(0, 0, 0);
	glVertex3f(1, 0, 0);
	glVertex3f(0, 1, 0);
	glVertex3f(1, 1, 0);
	glVertex3f(0, 0, 1);
	glVertex3f(1, 0, 1);
	glVertex3f(0, 1, 1);
	glVertex3f(1, 1, 1);

	glEnd();
	glEndList();
}


void DrawGlobalCoordinateSystem(void)
{

	glColor3f(1, 0, 0);
	glBegin(GL_LINES);
	glVertex3f(0, 0, 0);
	glVertex3f(2, 0, 0);
	glVertex3f(2, -0.25, 0.25);
	glVertex3f(2, 0.25, -0.25);
	glVertex3f(2, -0.25, -0.25);
	glVertex3f(2, 0.25, 0.25);

	glEnd();
	glColor3f(0, 1, 0);
	glBegin(GL_LINES);
	glVertex3f(0, 0, 0);
	glVertex3f(0, 2, 0);
	glVertex3f(0, 2, 0);
	glVertex3f(0.25, 2, 0);
	glVertex3f(0, 2, 0);
	glVertex3f(-0.25, 2, 0.25);
	glVertex3f(0, 2, 0);
	glVertex3f(-0.25, 2, -0.25);

	glEnd();
	glColor3f(0, 0, 1);
	glBegin(GL_LINES);
	glVertex3f(0, 0, 0);
	glVertex3f(0, 0, 2);
	glVertex3f(-0.25, -0.25, 2);
	glVertex3f(0.25, 0.25, 2);
	glVertex3f(-0.25, -0.25, 2);
	glVertex3f(0.25, -0.25, 2);
	glVertex3f(-0.25, 0.25, 2);
	glVertex3f(0.25, 0.25, 2);

	glEnd();

	glColor3f(1, 1, 1);
}

