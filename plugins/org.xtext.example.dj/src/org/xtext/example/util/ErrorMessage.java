package org.xtext.example.util;

import org.eclipse.emf.ecore.EObject;

public class ErrorMessage
{
  private String message;
  private EObject source;
  private Integer feature;
  private boolean isWarning;

  public ErrorMessage(String message, EObject source, Integer feature, boolean isWarning)
  {
    this.message = message;
    this.source = source;
    this.feature = feature;
    this.isWarning = isWarning;
  }

  public ErrorMessage(String message, Integer feature, boolean isWarning)
  {
    this(message, null, feature, isWarning);
  }

  public ErrorMessage(String message, EObject source)
  {
    this(message, source, null, false);
  }

  public ErrorMessage(String message, EObject source, Integer feature)
  {
    this(message, source, feature, false);
  }

  public ErrorMessage(String message, Integer feature)
  {
    this(message, null, feature, false);
  }

  public ErrorMessage(String message)
  {
    this(message, null, null);
  }

  public String getMessage()
  {
    return this.message;
  }

  public EObject getSource()
  {
    return this.source;
  }

  public Integer getFeature()
  {
    return this.feature;
  }

  public boolean isWarning()
  {
    return this.isWarning;
  }
}